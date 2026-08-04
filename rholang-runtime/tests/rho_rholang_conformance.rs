//! # Rholang ⟷ Rholang differential conformance suite (option C, Stage 0)
//!
//! ## Why this file exists
//!
//! Rholang ("MeTTaIL *is* Rholang 1.4") currently carries **two** implementations of the same
//! ground-data algebra:
//!
//! | # | Implementation | Where | Who runs it |
//! |---|---|---|---|
//! | ① | the `![{ … }]` **fold bodies** | `languages/src/rholang.rs` | MeTTaIL's Dovetail/e-graph (REPL, simulation) |
//! | ② | the **lowering** to `rhoapi::Par` | `rholang-runtime/src/rholang_ast.rs` | f1r3node's real reducer (`rholang/…/reduce.rs`) |
//!
//! Two implementations of one algebra can — and demonstrably **do** — diverge. This suite is the
//! *measurement instrument* for that divergence and the *acceptance gate* for the refactor that
//! removes it ("option C — different carriers, ONE evaluator": keep MeTTaIL's `Arc`-based,
//! hash-consed, moniker-bound AST as the carrier, but make the f1r3node consensus reducer the
//! sole *evaluator* of every operation Rholang already has).
//!
//! ## The invariant
//!
//! For a Rholang source expression `e`:
//!
//! ```text
//!                    ┌──────────────── ① fold ────────────────┐
//!                    │  Dovetail e-graph saturation over the  │
//!                    │  `![{…}]` native bodies                │──▶ Rholang surface display
//!   parse(e) ──▶ Proc┤                                        │            ║
//!    (ONE parse)     │                                        │            ║  must be EQUAL
//!                    │  lower_rholang_proc ▸ rhoapi::Par      │            ║
//!                    └──────────────── ② reduce ──────────────┘──▶ RuntimeObservationValue
//!                                                                          ║
//!                                                        render_as_rholang ╝
//! ```
//!
//! Both sides start from the **same** parsed `Proc`, so a parser/disambiguation difference can
//! never masquerade as a semantic one.
//!
//! ### The comparison is on VALUES, not carriers
//!
//! Carrier binding (making Rholang's categories literally be `rhoapi` types) is **blocked** and
//! deliberately not attempted: `models/src/rust/rhoapi_ext.rs:64-76` documents that `Ord` on `Par`
//! includes `locally_free` while the hand-written `PartialEq` ignores it — *"the wart is
//! load-bearing … do NOT 'fix' it"* — and MeTTaIL's collections and e-graph require `Ord` ⟷ `Eq`
//! agreement. So the two sides keep different carriers, and conformance is asserted on the
//! **observable value rendered in Rholang surface syntax**. [`render_as_rholang`] is that adapter;
//! it is part of the specification, not a convenience.
//!
//! ### The reducer is NORMATIVE
//!
//! Where the two disagree, `rholang/src/rust/interpreter/reduce.rs` (the consensus semantics) is
//! right and Rholang is wrong — "rholang IS rholang". Every divergence below is therefore recorded
//! as a pair:
//!
//! * a **witness** test (runs, green) that pins TODAY's divergent behaviour with citations to both
//!   sides, so the divergence is actively observed and cannot silently change; and
//! * a **target** test (`#[ignore]`d) that asserts the RHOLANG-normative behaviour. It fails today.
//!   The refactor stages flip it green by *deleting* the MeTTaIL-side implementation, and that flip
//!   is the proof the refactor preserved semantics.
//!
//! Removing an `#[ignore]` therefore always comes with deleting or amending its witness twin; the
//! witness doc-comment says which.
//!
//! ## The divergence ledger (measured 2026-07-25, not hypothesized)
//!
//! | ID | Subject | Rholang fold ① | Rholang reducer ② | Closed by | Status |
//! |---|---|---|---|---|---|
//! | **A** | `Int` overflow | the **`error`** term (was: silently **`0`**) | wraps (`i64::MIN`) | C1 | open (fabrication fixed) |
//! | **A2** | `Int` division / remainder by zero | the **`error`** term (was: silently **`0`**) | `ReduceError("Division by zero")` | — | ★ CLOSED |
//! | **B** | `+` on a **runtime-bound** string | rests unreduced | `OperatorNotDefined { op: "+", other_type: "string" }` | C1 | open |
//! | **C** | `l.nth(i)` out of bounds, and `nth` on a plain (`BigInt`) index | the `error` term, all carriers (was: **process abort** / `error`) | recoverable `ReduceError` | C1 | open (fold half CLOSED) |
//! | **D** | `Fixed` arithmetic on **mismatched scales** | rescales | `OperatorExpectedError` | C1 | open |
//! | **E** | canonical **collection order** for `toByteArray` | protobuf byte order | `ScoredTerm` value order | C2 | ★ CLOSED |
//! | **F** | `.toByteArray()` | a hex `GString` — and unreachable from source | a real `GByteArray` | C2 | ★ CLOSED |
//! | **G** | `Pathmap` / zippers | homogeneous trie carriers + 20+ methods | native `EPathmapBody` / `EZipperBody` | C4 | ★ CLOSED |
//! | **H** | `==` / `!=` on **`Bool`** | `Bool` (was: `error`, no fold arm) | `Bool(true)` | — | ★ CLOSED |
//! | **I** | a numeral's **carrier** depends on syntax (`@(1)`:`Int` vs `@1`:`BigInt`, `5u32`:`BigInt`) | `*(@(1)) + 2` ⟹ `error` | Rholang has ONE integer | the GRAMMAR (partitioned literal domains), NOT the WPDA projection | ★ CLOSED |
//! | **J** | `x!()` satisfies `for(@y <- x)` | fires, `y = []` | arity-checked COMM: rests | C1 | open |
//! | **K** | a `where` guard the host CANNOT DECIDE | the COMM **rests** (decline read as `false`) | decides it and **fires** | #33 stage C | open |
//! | **L** | canonical **`Set`/`Map` order** | **lexicographic** by rendered element (`Set(10, 2)`) | `ScoredTerm` **value** order (`Set(2, 10)`) | — | open |
//!
//! `L` was **discovered by C1's canonical-order check (2026-07-26)** and is the same lesson as
//! `H`: it survived because every fixture in the suite used single-digit integers, where
//! lexicographic and value order coincide. It is a LITERAL-level divergence, not a method-level
//! one — `Set(10, 2)`, with no method call in it at all, already renders differently on the two
//! sides — so C1 neither caused it nor can close it. See
//! `divergence_l_witness_collection_order_is_lexicographic_in_the_fold`.
//!
//! `H` was **discovered by this suite**; `I` and `J` were discovered by the burndown described
//! immediately below; **`K` was discovered by pointing this suite at a `where` guard for the
//! first time** (#33 stage D, 2026-07-25). None of the four is in the original `§17.11`
//! inventory.
//!
//! ### ⚠ Why `K` took until 2026-07-25 to surface
//!
//! Not for want of a guard test — `rho_matches_differential.rs` has locked the host and the
//! machine to the same *verdict* for `matches` guards since M-1b. But its agreement property is
//! one-directional **by design**: a host `None` is an accepted escape hatch, on the reasoning
//! that "`eval_guard_bool`'s callers treat an undecided guard as *do not fire* host-side". So the
//! VERDICT was locked and the NORMAL FORM was never compared, and this suite — the one instrument
//! that compares normal forms — had never been aimed at a guard. The permissive reading of the
//! guard lane survived by never having been measured, which is the useful lesson: an invariant
//! that is asserted in a doc comment and nowhere in a test is a hypothesis.
//!
//! ### The boundary of `K`: the GUARD lane, not the FORMULA lane
//!
//! Rholang spells `or` at two levels, and `K` belongs to exactly one of them. The guard-level
//! `or` (`Proc::Or` ⟶ `EOr`, an EVALUATED expression) is `eval_guard_disposition`'s left-strict
//! arm and is where `K` lives. The formula-level `or` (`FormulaShape::Disjunction` ⟶
//! `ConnOrBody`, a MATCHED pattern) is `formula::kleene_or`, which is full Kleene — it already
//! applies `unknown ∨ true = true`, the very rule the guard lane refuses as unsound.
//!
//! That looks like a live unsoundness and **is not**:
//! `formula_level_disjunction_agrees_where_the_guard_level_or_diverges` measures all four
//! reachable `kleene_or` cells against the machine and they agree, including `kleene_or(?, T)`.
//! A pattern is never evaluated, so f1r3node's strict `EOr` — the thing that blocks stage B2 —
//! has nothing to act on. ★ The repair therefore belongs in `receive::eval_guard_disposition`;
//! changing `formula::kleene_or` would be fixing the lane that is already correct.
//!
//! ### ⚠ The pins this suite replaced did not pin anything — now FIXED
//!
//! `languages/tests/rholang_tests.rs::assert_reduces_to` — the helper behind most of that file's
//! Rholang semantics tests — reached its verdict through a disjunction ending in
//! `bag_multiset_eq(nf, expected)`, and `bag_multiset_eq` returned
//! `to_sorted_bag_elements(a) == to_sorted_bag_elements(b)`, i.e. `None == None` ⟹ **`true`**,
//! whenever neither side was a `#{…}#` bag literal. Measured 2026-07-25:
//! `assert_reduces_to("1 + 2", "999")` **passed**.
//!
//! The comparator is now guarded (an inapplicable comparator answers `false`, never `true`) and
//! the resulting 34 red tests were burned down to zero. That burndown is what surfaced divergences
//! `I` and `J`, the `nth` panic + index-carrier halves of `C`, the fold-vs-redex `error` poisoning
//! (`*(@(1)) == 1` ⟹ `error`), the never-lowered nullary folds (`Map()` never became `{}`), and
//! the join-row whole-message binder (`for(@x <- c1 & …)` bound the payload LIST). The vacuity
//! guarantee itself is pinned by `rholang_tests.rs::comparator_integrity`.
//!
//! This suite still compares with `assert_eq!` on an explicitly written expected value and never
//! through a fuzzy helper.
//!
//! ### ✔ Divergence A is RESOLVED UPSTREAM (2026-07-29) — the reducer no longer wraps
//!
//! f1r3node used to disagree with **itself** about integer `+`:
//!
//! | Evaluator | `i64::MAX + 1` (before 2026-07-29) | Site |
//! |---|---|---|
//! | consensus reducer | **wrapped** → `i64::MIN` | `rholang/src/rust/interpreter/reduce.rs` `combine_plus`, `lhs.wrapping_add(rhs)` |
//! | guard evaluator | **errored** | `rho-pure-eval/src/eval.rs` `int_binop_checked("+", …, i64::checked_add)` |
//!
//! …and, within the reducer itself, `*` and unary `-` were CHECKED while `+` and `-` wrapped: two
//! opposite dispositions for one partiality, selected by which operator the deployer happened to
//! write.
//!
//! **RULED 2026-07-29: "fix it — checked, with a clear error."** `combine_plus` and
//! `combine_minus` now use `checked_add` / `checked_sub` and raise
//! `ReduceError("Arithmetic overflow in addition: {lhs} + {rhs} is not representable as an Int
//! (64-bit signed)")`, naming the operation AND both operands. Every `Int` operator in the reducer
//! now answers the same way when its result is not representable, and the reducer now agrees with
//! `rho-pure-eval`. Pinned upstream by `rholang/tests/reduce_spec.rs`
//! (`eval_expr_should_return_error_for_{addition,subtraction}_overflow`,
//! `every_int_operator_refuses_a_result_it_cannot_represent`) and end-to-end by
//! `rholang/tests/rholang_numeric_eval_spec.rs`.
//!
//! ⚠ **That fix is consensus-visible**: a program whose `Int` addition or subtraction overflows
//! now raises where it previously produced a wrapped value. Its measured blast radius is the
//! "detect overflow by observing the wrap" idiom in the genesis contracts
//! (`NonNegativeNumber.rho`'s `if (v + x >= v)`, and `MakeMint.rho`'s `deposit` through it), whose
//! total replacement is to guard BEFORE adding — `if (x <= 9223372036854775807 - v)`.
//!
//! What this suite asserts is unchanged and remains MeTTaIL's own part: Rholang must not
//! contribute a **third arithmetic answer**, and must inherit whichever f1r3node evaluator its
//! lowering routes to — process position ⟶ `reduce.rs`, guard position ⟶ `rho-pure-eval`. Those
//! two now agree, so "inherit the machine's answer" has one target instead of two. The 2026-07-25
//! fix had already removed the part that was indefensible on its own terms — a *checked* operation
//! FABRICATING `Default::default()` and presenting it as the answer — leaving `error`, which is
//! the absence of an answer rather than a competing one.
//!
//! ### ★ Float ÷0 — NO LONGER A DIVERGENCE. MeTTaIL answers IEEE-754, as upstream does.
//!
//! | Evaluator | `1.0 / 0.0` | `-1.0 / 0.0` | `0.0 / 0.0` |
//! |---|---|---|---|
//! | f1r3node's reducer (`reduce.rs` `combine_div`, `GDouble` arm) | `+Inf` | `-Inf` | `NaN` |
//! | MeTTaIL's Rholang (`languages/src/rholang.rs`, `Div`'s `CastFloat` arm) | `+Inf` | `-Inf` | `NaN` |
//!
//! **RULED 2026-07-29, REVERSING an earlier ruling of the same day** that had kept a refusal here
//! (recorded in `ffdc3ad1`, whose text this section replaces). The governing rule is *upstream is
//! a floor on SEMANTICS, not a ceiling on DIAGNOSTICS*: a program upstream **accepts** must be
//! accepted, and must compute the **same value**. The BUG-FIX carve-out licenses divergence only
//! where upstream is *wrong*, and ⚠ IEEE 754 §7.3 **defines** finite-non-zero ÷ 0 as the
//! correctly-signed infinity and `0/0` as a `NaN` — so upstream is correct, the carve-out is
//! unavailable, and refusing rejected a program upstream accepts. The reversal and the rebuttal of
//! each of the earlier ruling's three arguments are recorded at the arm itself.
//!
//! ⚠ **Two residual divergences remain, and neither is division's.** `CanonicalFloat64`
//! (`runtime/src/canonical_float.rs:35-42`) maps `-0.0` to `+0.0` and every `NaN` to one bit
//! pattern so that terms have a well-defined `Eq`/`Hash`/`Ord`. So `x / -0.0` answers `+Inf` here
//! and `-Inf` upstream — `-0.0` is not a representable `Float` term at all — and a produced `NaN`
//! carries `f64::NAN`'s bits rather than the hardware's. Both are properties of the CARRIER.
//!
//! ★★ **RULING EXTENDED to every float arithmetic arm.** The three siblings that still refused an
//! IEEE indeterminate form — `Add`, `Sub`, `Mul` — were ruled the same way on 2026-07-29 and now
//! answer IEEE too, and a FOURTH was found by deriving the arm inventory instead of working from
//! the list: the `Neg` rule's float arm reached `safe_neg` *implicitly*, through the operator
//! rewrite, and stranded `-(0.0 / 0.0)` as a STUCK TERM rather than answering `error`. All five
//! sites (`Add`, `Sub`, `Mul`, `Div`, `Neg`) now route through one adapter,
//! `mettail_runtime::nan_is_a_value`, so the `UndefinedReason::NotANumber` match lives in exactly
//! one place instead of being copied five times. `SafeArith`'s own NaN policy is untouched — the
//! tropical and log-domain semirings depend on it, and the adapter is opt-in per call site. See
//! [`every_float_arithmetic_arm_answers_ieee754_for_every_indeterminate_form`] for the case set
//! derived from IEEE 754 §6.2/§6.3/§7.2/§7.4.
//!
//! `%` needs no change and that is now MEASURED on both sides
//! ([`float_modulo_is_refused_by_both_evaluators_so_it_needs_no_ruling`]): MeTTaIL's `Mod` has no
//! float arm and upstream's `combine_mod` refuses `(GDouble, GDouble)` outright, so no program's
//! acceptance differs.
//!
//! ⚠★ **The rulings ACTIVATED a latent comparison divergence, which is FILED not fixed.** `NaN` was
//! previously unreachable, so the comparison operators' `NaN` behaviour was unobservable. It is
//! observable now: `NaN == NaN` is `true` here and `false` upstream, and `NaN > 1.0` is `true` here
//! and `false` upstream, because the arms compare `CanonicalFloat64` values whose `PartialEq` is
//! reflexive on `NaN` and whose `Ord` sorts `NaN` last — deliberately, so terms have a usable
//! `Eq`/`Hash`/`Ord`. Measured and pinned in
//! [`nan_comparisons_follow_the_carrier_not_ieee754_and_that_is_filed`], which also explains why
//! the two-line arm-level fix is a semantics decision rather than a bug fix.
//!
//! ## Operational note: fold panics ABORT the process here
//!
//! `catch_unwind` cannot contain a panic raised inside a Dovetail fold in this workspace: the
//! unwinder crosses Cranelift-compiled frames (`[profile.dev] codegen-backend = "cranelift"`,
//! workspace `Cargo.toml:79`) and dies with `fatal runtime error: failed to initiate panic,
//! error 5, aborting`. That is why every fold-side failure disposition in Rholang is a VALUE
//! (`Proc::Err`) and never a panic, and why
//! [`divergence_c_closed_nth_is_total_and_carrier_agnostic`] can assert an out-of-range `nth`
//! in-process: if the panic were back, the test binary would die instead of failing.

use std::sync::Arc;

use mettail_languages::rholang::{Name, Proc, RholangLanguage, RholangTerm, RholangTermInner, Str};
use mettail_rholang_runtime::fold_contract::fold_definitions_for;
use mettail_rholang_runtime::rholang_ast::{clear_held_fold_sites, take_held_fold_sites};
use mettail_rholang_runtime::run::run_installed_program_with_call_definitions_and_read_runtime_values;
use mettail_rholang_runtime::{lower_rholang_proc, RholangAstLowerError, RHOLANG_BAG_ABI_TAG};
use mettail_runtime::{clear_var_cache, RuntimeObservationValue};
use models::rhoapi::Par;

// ════════════════════════════════════════════════════════════════════════════════════════════════
// Harness
// ════════════════════════════════════════════════════════════════════════════════════════════════

/// Dovetail saturation bounds — the same values the Rholang language test oracle uses
/// (`languages/tests/rholang_tests.rs::oracle`), so a fold that converges there converges here.
const DOVETAIL_ITERS: usize = 256;
const DOVETAIL_NODES: usize = 4_000_000;

/// Successor-edge bound for the COMM+fold fixpoint in [`fold_program`]. Generous: every
/// terminating program in this suite settles in fewer than ten steps.
const COMM_STEP_BOUND: usize = 64;

/// The ONE parse both sides share. `parse_via_wpda` is the disambiguated best-parse entry the
/// production AST-first lowering path uses (`rholang-runtime/tests/rho_rholang_ast.rs::parse_lower`).
fn parse(source: &str) -> Proc {
    clear_var_cache();
    Proc::parse_via_wpda(source)
        .unwrap_or_else(|err| panic!("rholang parse failed for {source:?}: {err}"))
}

/// ① the FOLD side: reduce `proc` to a Dovetail normal form and render it in Rholang surface
/// syntax.
///
fn fold(proc: &Proc) -> Result<String, String> {
    let term = RholangTerm(RholangTermInner::Proc(proc.clone()));
    RholangLanguage::dovetail_normal_term(&term, DOVETAIL_ITERS, DOVETAIL_NODES)
        .map(|normal_form| normal_form.to_string())
        .map_err(|err| format!("dovetail: {err}"))
}

/// ① the FOLD side for a whole PROGRAM: a bounded COMM+normalize fixpoint.
///
/// `dovetail_normal_term` alone folds native operators but does not fire a rendezvous, so a
/// program shaped `@("c")!(v) | for (@x <- @("c")) { … }` needs `Proc::try_comm_once` interleaved
/// with folding. This is exactly the `try_comm_anywhere` / `normalize_anywhere` loop the Rholang
/// language test oracle runs (`languages/tests/rholang_tests.rs:331` `run_fixpoint`), reduced to
/// the single-successor case this suite needs.
fn fold_program(proc: &Proc) -> Result<String, String> {
    let mut current = proc.clone();
    for _ in 0..COMM_STEP_BOUND {
        // Fold first: a send payload must be a value before the rendezvous delivers it.
        let term = RholangTerm(RholangTermInner::Proc(current.clone()));
        if let Ok(normal_form) =
            RholangLanguage::dovetail_normal_term(&term, DOVETAIL_ITERS, DOVETAIL_NODES)
        {
            if let Some(folded) = proc_of(normal_form.as_ref()) {
                if !folded.term_eq(&current) {
                    current = folded;
                    continue;
                }
            }
        }
        match current.try_comm_once() {
            Some(next) if !next.term_eq(&current) => current = next,
            _ => return Ok(current.to_string()),
        }
    }
    Err(format!("comm+fold fixpoint did not settle within {COMM_STEP_BOUND} steps"))
}

/// The FOLD side, returning the normal form as a `Proc` rather than its rendered string, so a test
/// can ask about structural identity (`BoundTerm::term_eq`, `Proc::semantic_hash`) and not only
/// about display.
fn fold_to_proc(source: &str) -> Proc {
    let owned = parse(source);
    let label = source.to_string();
    let term = RholangTerm(RholangTermInner::Proc(owned));
    let normal_form = RholangLanguage::dovetail_normal_term(&term, DOVETAIL_ITERS, DOVETAIL_NODES)
        .unwrap_or_else(|err| panic!("dovetail failed for {label:?}: {err}"));
    proc_of(normal_form.as_ref()).unwrap_or_else(|| panic!("{label:?} did not fold to a Proc"))
}

/// Unwrap a boxed `RholangTerm` back to its `Proc` alternative (`None` for a non-`Proc` category
/// or an `Ambiguous` residue).
fn proc_of(term: &dyn mettail_runtime::Term) -> Option<Proc> {
    term.as_any()
        .downcast_ref::<RholangTerm>()
        .and_then(|typed| match &typed.0 {
            RholangTermInner::Proc(proc) => Some(proc.clone()),
            _ => None,
        })
}

/// ② the REDUCE side: lower `@("OUT")!(<expr>)` and evaluate it on the real f1r3node reducer,
/// returning every ground value resting on `@"OUT"`.
///
/// Width/precision folds (`int(a,w)`, `uint`, `float`, `fixed`, `bigint`, `bigrat`) have no
/// Rholang operator, so the lowering lifts each into a fold-contract trampoline and records a
/// `FoldSpec`; the specs are materialized into system-process `Definition`s here exactly as the
/// production exec path does (`rholang-runtime/src/backend.rs:1335`).
async fn reduce(proc: &Proc) -> Result<Vec<RuntimeObservationValue>, String> {
    reduce_program(&Proc::POutput(
        Arc::new(Name::NQuote(Arc::new(Proc::CastStr(Arc::new(Str::StringLit(
            "OUT".to_string(),
        )))))),
        Arc::new(proc.clone()),
    ))
    .await
}

/// [`reduce`] for a program that already carries its own sends/receives.
async fn reduce_program(program: &Proc) -> Result<Vec<RuntimeObservationValue>, String> {
    clear_held_fold_sites();
    let par = lower_rholang_proc(program).map_err(|err| lower_error_message(&err))?;
    let definitions = fold_definitions_for(&take_held_fold_sites())
        .expect("#36 S4/S5: the band allocation is pairwise distinct for a single language");
    run_installed_program_with_call_definitions_and_read_runtime_values(
        &Par::default(),
        &par,
        definitions,
        "OUT",
    )
    .await
    .map_err(|err| format!("reduce: {err}"))
}

/// A stable, greppable rendering of a lowering failure: `unsupported: <named construct>` for the
/// fail-closed `UnsupportedProc` arm (`rholang-runtime/src/rholang_ast.rs::unsupported_construct_name`),
/// the debug form otherwise.
fn lower_error_message(err: &RholangAstLowerError) -> String {
    match err {
        RholangAstLowerError::UnsupportedProc(name) => format!("unsupported: {name}"),
        other => format!("lower: {other:?}"),
    }
}

// ════════════════════════════════════════════════════════════════════════════════════════════════
// The carrier adapter: `RuntimeObservationValue` ⟶ Rholang surface syntax
// ════════════════════════════════════════════════════════════════════════════════════════════════

/// Render a reducer observation in Rholang's own surface syntax, so it can be compared with a fold
/// normal form's `Display`.
///
/// This is the **specification of the carrier correspondence**, not a test convenience: it states,
/// value by value, which `rhoapi` ground datum Rholang considers to *be* which Rholang value.
/// Deliberately total-by-panic on the shapes this suite does not yet specify, so an unspecified
/// carrier can never be silently accepted as conformant.
fn render_as_rholang(value: &RuntimeObservationValue) -> String {
    match value {
        // The `Int` category ⟷ `ExprInstance::GInt`. ★ CORRECTED 2026-07-25 (divergence I):
        // this is the carrier of a PLAIN Rholang integer literal — `1`, `1i32`, `1i64`, `1u32`
        // — exactly as f1r3node's `normalize_ground` maps them, as well as of `int(a, w)`.
        RuntimeObservationValue::Int(literal) => literal.to_string(),
        // ⚠ The comment that stood here — "a plain Rholang integer literal is arbitrary-precision
        // (Rholang 1.4's default), so it rides as `GBigInt`" — was FACTUALLY WRONG, and stating
        // it in the conformance suite is part of why divergence I survived so long.
        // `normalize_ground` sends a bare numeral to `GInt`; only the `…n` spelling is `GBigInt`.
        // `GBigInt` is therefore rendered with the `n` tail its own grammar requires, which is
        // also what the fold's `Display` now emits (Stage C).
        RuntimeObservationValue::BigIntBytes(bytes) => {
            format!("{}n", num_bigint::BigInt::from_signed_bytes_be(bytes))
        },
        RuntimeObservationValue::Bool(literal) => literal.to_string(),
        // Rholang `Str` displays quoted; `{:?}` on `&str` is the same escaping Rholang's generated
        // `Display` uses for the shapes this suite covers (no embedded quotes/backslashes).
        RuntimeObservationValue::Text(text) => format!("{text:?}"),
        // `GDouble` carries the IEEE-754 bit pattern. `{:?}` keeps the trailing `.0` Rholang's
        // `Float` display emits (`4.0`, not `4`).
        RuntimeObservationValue::DoubleBits(bits) => format!("{:?}", f64::from_bits(*bits)),
        RuntimeObservationValue::BigRationalBytes { numerator, denominator } => format!(
            "{}/{}",
            num_bigint::BigInt::from_signed_bytes_be(numerator),
            num_bigint::BigInt::from_signed_bytes_be(denominator)
        ),
        RuntimeObservationValue::FixedPointBytes { unscaled, scale } => {
            render_fixed_point(unscaled, *scale)
        },
        RuntimeObservationValue::List(items) => {
            format!("[{}]", render_all(items).join(", "))
        },
        RuntimeObservationValue::Set(items) => {
            format!("Set({})", render_all(items).join(", "))
        },
        RuntimeObservationValue::Map(entries) => format!(
            "{{{}}}",
            entries
                .iter()
                .map(|(key, mapped)| format!(
                    "{}:{}",
                    render_as_rholang(key),
                    render_as_rholang(mapped)
                ))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        RuntimeObservationValue::Tuple(items) => {
            format!("({})", render_all(items).join(", "))
        },
        other => panic!(
            "render_as_rholang: no Rholang surface form is specified for {other:?}; \
             add one deliberately rather than letting an unspecified carrier pass as conformant"
        ),
    }
}

fn render_all(values: &[RuntimeObservationValue]) -> Vec<String> {
    values.iter().map(render_as_rholang).collect()
}

/// Lowercase hex of a byte slice — the readable form of a `GByteArray` observation. (`languages`
/// carried a `hex` dependency solely for the retired wire fork's goldens; this suite does not
/// reintroduce one for six lines.)
fn hex_of(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

/// Rholang's `Fixed` surface form: the unscaled integer with a decimal point `scale` digits from
/// the right, suffixed `p<scale>` (`3p0`, `3.3p1`, `1.00p2`).
fn render_fixed_point(unscaled: &[u8], scale: u32) -> String {
    let value = num_bigint::BigInt::from_signed_bytes_be(unscaled);
    if scale == 0 {
        return format!("{value}p0");
    }
    let negative = value < num_bigint::BigInt::from(0);
    let digits = value.magnitude().to_string();
    let scale = scale as usize;
    let padded = if digits.len() <= scale {
        format!("{}{}", "0".repeat(scale + 1 - digits.len()), digits)
    } else {
        digits
    };
    let split = padded.len() - scale;
    format!(
        "{}{}.{}p{scale}",
        if negative { "-" } else { "" },
        &padded[..split],
        &padded[split..]
    )
}

// ════════════════════════════════════════════════════════════════════════════════════════════════
// The conformance assertion
// ════════════════════════════════════════════════════════════════════════════════════════════════

/// Assert the consensus path: `reduce(lower(e))` agrees with the human-written `expected`
/// Rholang surface form.
///
/// This is the only semantic assertion for `MethodCall`.  The grammar intentionally retains a
/// method call as `(receiver, identifier text, ordered arguments)`; f1r3node's method table is the
/// sole evaluator and sole registry for method names and arities.
async fn assert_reducer_result(source: &str, expected: &str) {
    let proc = parse(source);
    let observed = reduce(&proc)
        .await
        .unwrap_or_else(|err| panic!("{source:?}: the Rholang REDUCE side failed: {err}"));
    let [value] = observed.as_slice() else {
        panic!("{source:?}: expected exactly one observation on @\"OUT\", got {observed:?}");
    };
    let rendered = render_as_rholang(value);
    assert_eq!(
        rendered, expected,
        "{source:?}: the Rholang REDUCER (f1r3node reduce.rs) disagrees with the specified value \
         (raw observation: {value:?})"
    );
}

/// The suite's differential assertion for constructs that still have an independent MeTTaIL
/// fold: `fold(e)`, `reduce(lower(e))`, and the human-written `expected` form all agree.
///
/// `expected` is stated explicitly rather than only asserting `fold == reduce`, so a *mutual*
/// drift (both sides changing together) still fails.
async fn assert_conformant(source: &str, expected: &str) {
    let proc = parse(source);

    let folded = fold(&proc)
        .unwrap_or_else(|err| panic!("{source:?}: the Rholang fold did not converge: {err}"));
    assert_eq!(
        folded, expected,
        "{source:?}: the Rholang FOLD (languages/src/rholang.rs `![{{…}}]` bodies) \
         disagrees with the specified value"
    );

    assert_reducer_result(source, expected).await;
}

// ════════════════════════════════════════════════════════════════════════════════════════════════
// PART 1 — the conformant surface (these MUST stay green through every refactor stage)
// ════════════════════════════════════════════════════════════════════════════════════════════════

/// Integer arithmetic on the two integer carriers. ★ CORRECTED 2026-07-25 (divergence I): a plain
/// Rholang integer literal is **`Int`**, riding `GInt` on the machine and `i64` in the fold, exactly
/// as f1r3node's `normalize_ground` maps it. Only the `…n` spelling is arbitrary-precision, riding
/// `GBigInt` / `CanonicalBigInt` and displaying with its mandatory `n` tail.
#[tokio::test(flavor = "multi_thread")]
async fn conformance_int_arithmetic() {
    assert_conformant("1 + 2", "3").await;
    assert_conformant("5 - 3", "2").await;
    assert_conformant("3 * 4", "12").await;
    assert_conformant("10 / 2", "5").await;
    assert_conformant("10 % 3", "1").await;
    assert_conformant("-7", "-7").await;
    assert_conformant("0 - 2", "-2").await;
}

/// The arbitrary-precision carrier, reached ONLY through the `…n` spelling.
#[tokio::test(flavor = "multi_thread")]
async fn conformance_bigint_arithmetic() {
    assert_conformant("1n + 2n", "3n").await;
    assert_conformant("5n - 3n", "2n").await;
    assert_conformant("3n * 4n", "12n").await;
    // Beyond `i64`, where the carrier is the whole point.
    assert_conformant("9223372036854775807n + 1n", "9223372036854775808n").await;
}

/// Fixed-width integer arithmetic (`int(a, w)` ⟷ `GInt`), inside the non-overflowing range.
/// Overflow is divergence **A**.
#[tokio::test(flavor = "multi_thread")]
async fn conformance_fixed_width_int_arithmetic() {
    assert_conformant("int(5, 64)", "5").await;
    assert_conformant("int(-3, 64)", "-3").await;
    assert_conformant("int(1, 64) + int(2, 64)", "3").await;
    assert_conformant("int(2, 64) * int(3, 64)", "6").await;
    assert_conformant("uint(5, 32)", "5").await;
}

/// The six relational operators on integers, and on strings.
#[tokio::test(flavor = "multi_thread")]
async fn conformance_comparisons() {
    assert_conformant("1 < 2", "true").await;
    assert_conformant("2 <= 2", "true").await;
    assert_conformant("3 > 4", "false").await;
    assert_conformant("3 >= 3", "true").await;
    assert_conformant("1 == 1", "true").await;
    assert_conformant("1 != 2", "true").await;
    assert_conformant(r#""a" == "a""#, "true").await;
    assert_conformant(r#""a" < "b""#, "true").await;
}

/// Boolean connectives. Boolean `==`/`!=` is divergence **H**.
#[tokio::test(flavor = "multi_thread")]
async fn conformance_boolean_connectives() {
    assert_conformant("true and false", "false").await;
    assert_conformant("true or false", "true").await;
    assert_conformant("not true", "false").await;
}

/// IEEE-754 doubles.
#[tokio::test(flavor = "multi_thread")]
async fn conformance_float_arithmetic() {
    assert_conformant("1.5 + 2.5", "4.0").await;
    assert_conformant("1.5 < 2.5", "true").await;
}

/// Fixed-point arithmetic at EQUAL scales. Mismatched scales are divergence **D**.
#[tokio::test(flavor = "multi_thread")]
async fn conformance_fixed_point_arithmetic_at_equal_scale() {
    assert_conformant("1p0 + 2p0", "3p0").await;
    assert_conformant("10p1 / 3p1", "3.3p1").await;
    assert_conformant("fixed(1, 2)", "1.00p2").await;
}

/// String concatenation via `+` on **statically ground** operands. The runtime-bound case is
/// divergence **B**; the parity here is bought by a lowering shim
/// (`rholang-runtime/src/rholang_ast.rs:930-942`, `is_single_gstring_value`) that rewrites `+` to
/// Rholang's `++` (`EPlusPlus`) only when both operands are already `GString` leaves.
#[tokio::test(flavor = "multi_thread")]
async fn conformance_ground_string_concat() {
    assert_conformant(r#""con" + "cat""#, r#""concat""#).await;
    assert_conformant(r#""hello " + "world""#, r#""hello world""#).await;
}

/// Collection literals and their canonical ordering. `List` keeps source order; `Set` and `Map`
/// are canonically sorted, and MeTTaIL's `Proc: Ord` agrees with Rholang's `ScoredTerm` order for
/// non-negative integers (they disagree for negatives — divergence **E**).
#[tokio::test(flavor = "multi_thread")]
async fn conformance_collection_literals() {
    assert_conformant("[1, 2, 3]", "[1, 2, 3]").await;
    assert_conformant("[]", "[]").await;
    assert_conformant("Set(1, 2, 3)", "Set(1, 2, 3)").await;
    assert_conformant("Set(3, 1, 2)", "Set(1, 2, 3)").await;
    assert_conformant("Set()", "Set()").await;
    assert_conformant("{1 : 10}", "{1:10}").await;
    assert_conformant("{2 : 20, 1 : 10}", "{1:10, 2:20}").await;
}

/// Structural equality on collections.
#[tokio::test(flavor = "multi_thread")]
async fn conformance_collection_equality() {
    assert_conformant("[1, 2, 3] == [1, 2, 3]", "true").await;
}

/// A rendezvous that carries a value: the payload is evaluated by the machine after the COMM, so
/// this pins that `lower_rholang_proc` + the reducer agree with the fold's COMM+normalize
/// fixpoint on a *runtime-bound* integer operand. (The string twin of this shape is divergence
/// **B**.)
#[tokio::test(flavor = "multi_thread")]
async fn conformance_runtime_bound_integer_add_after_comm() {
    let source = r#"@("c")!(1) | for (@s <- @("c")) { @("OUT")!(s + 2) }"#;
    let proc = parse(source);
    let observed = reduce_program(&proc)
        .await
        .expect("the program runs to rest");
    assert_eq!(
        observed.iter().map(render_as_rholang).collect::<Vec<_>>(),
        vec!["3".to_string()],
        "the machine evaluates `s + 2` on the COMM-delivered operand"
    );
}

// ════════════════════════════════════════════════════════════════════════════════════════════════
// PART 2 — the divergence ledger
//
// Each divergence has a WITNESS (runs, pins today's behaviour) and a TARGET (`#[ignore]`d, asserts
// the Rholang-normative behaviour). A refactor stage closes a divergence by removing its
// `#[ignore]`; the witness twin is then amended or deleted, as its doc-comment states.
// ════════════════════════════════════════════════════════════════════════════════════════════════

// ── A — integer overflow and integer division by zero ────────────────────────────────────────────

/// **Divergence A (witness) — BOTH SIDES NOW FAIL CLOSED on `i64` overflow.**
///
/// For `int(i64::MAX, 64) + int(1, 64)`:
///
/// | Implementation | Answer | Site |
/// |---|---|---|
/// | f1r3node consensus reducer | `ReduceError("Arithmetic overflow in addition: 9223372036854775807 + 1 …")` | `rholang/src/rust/interpreter/reduce.rs` `combine_plus`, `checked_add` |
/// | f1r3node guard evaluator | an error | `rho-pure-eval/src/eval.rs` `int_binop_checked` |
/// | MeTTaIL Rholang fold | the **`error`** term | `languages/src/rholang.rs` `Add` body ▸ `SafeArith::safe_add` ▸ `Err` ▸ `Proc::Err` |
///
/// **Amended 2026-07-25.** Until then the fold answered a silent **`0`**: its `Int` arm wrote
/// `(**a).clone() + (**b).clone()`, which reached a macro-emitted `impl std::ops::Add for Int`
/// whose failure path was `.unwrap_or_else(|| Int::NumLit(Default::default()))` — a *checked*
/// operation FABRICATING the category's `Default` on failure. That emitter fallback has been
/// deleted (`macros/src/gen/native/eval.rs`; no `std::ops::{Add,Sub,Mul,Div,Rem}` impl is emitted
/// for a category any more, so the fabrication is not expressible), and the fold arms now map
/// `SafeArith`'s failure onto `Proc::Err` — the disposition the `UInt32`/`BigInt`/`BigRat`/`Fixed`
/// arms already used for ÷0.
///
/// **Amended again 2026-07-29 — the RE-MEASUREMENT that closed the third answer.** This cell used
/// to assert that the machine *evaluated* the sum to `i64::MIN`:
///
/// ```text
///     let observed = reduce(&proc).await.expect("the machine evaluates the sum");
///     assert_eq!(observed…, vec![i64::MIN.to_string()],
///                "A: the consensus reducer wraps (reduce.rs wrapping_add)");
/// ```
///
/// Ruled 2026-07-29, `combine_plus` / `combine_minus` are CHECKED, so the reducer now REFUSES. The
/// three-way table above is down to two dispositions, and both are refusals: MeTTaIL answers the
/// `error` TERM (a value in the MeTTaIL lane), the machine raises a recoverable `ReduceError`.
/// Neither is a number, so the silent wrong-value hazard is gone on both sides — exactly the shape
/// divergence A2 already had for ÷0.
///
/// The residual divergence is the one this suite always said it was: the fold does not INHERIT the
/// evaluator its lowering routes to. That is still C1's to close — see
/// `divergence_a_target_int_overflow_inherits_the_f1r3node_evaluator`.
///
/// *Amend when C1 lands:* the fold body is gone, so both arms answer whatever `reduce.rs` answers.
#[tokio::test(flavor = "multi_thread")]
async fn divergence_a_witness_int_overflow_folds_to_the_error_term() {
    let source = "int(9223372036854775807, 64) + int(1, 64)";
    let proc = parse(source);

    assert_eq!(
        fold(&proc).expect("the fold converges"),
        "error",
        "A: Rholang's fold fails CLOSED on i64 overflow — never a fabricated value"
    );

    let err = reduce(&proc).await.expect_err(
        "the consensus reducer refuses an unrepresentable sum (checked since 2026-07-29)",
    );
    assert!(
        err.contains("Arithmetic overflow in addition"),
        "A: the consensus reducer must REFUSE, naming the operation and the operands — it wrapped \
         to {} until 2026-07-29, which is a different number presented as the sum. Got {err:?}",
        i64::MIN,
    );
    assert!(
        err.contains("9223372036854775807") && err.contains("+ 1"),
        "A: the message must name BOTH operands, which is what makes it actionable in a log. \
         Got {err:?}",
    );

    // ── THE CONTROL: a TOTAL sum still computes, on the machine, to the same value. If this
    // moves, the upstream fix broke addition rather than its overflow disposition.
    let total = parse("int(7, 64) + int(8, 64)");
    let observed = reduce(&total)
        .await
        .expect("a representable sum still evaluates");
    assert_eq!(
        observed.iter().map(render_as_rholang).collect::<Vec<_>>(),
        vec!["15".to_string()],
        "A CONTROL: checked addition must still add",
    );
}

/// **Divergence A2 — CLOSED 2026-07-25: `Int` division by zero fails closed.**
///
/// `int(1, 64) / int(0, 64)` folded to a silent **`0`** (same root as A: the fabricating
/// `impl Div for Int` fallback). It now folds to the `error` term, matching (a) its own
/// arbitrary-precision twin `1 / 0`, which always did, and (b) every other numeric arm of `Div`.
/// The reducer still raises `ReduceError("Division by zero")` — a *recoverable error* rather than
/// an error VALUE — so the two answers are not identical, but neither is a number: the silent
/// wrong-value hazard this witness existed for is gone.
///
/// Its target twin [`divergence_a2_target_int_division_by_zero_fails_closed`] is now GREEN.
#[tokio::test(flavor = "multi_thread")]
async fn divergence_a2_closed_int_division_by_zero_fails_closed() {
    let proc = parse("int(1, 64) / int(0, 64)");
    assert_eq!(
        fold(&proc).expect("the fold converges"),
        "error",
        "A2: `Int` ÷0 is the `error` term, not a fabricated 0"
    );
    let err = reduce(&proc)
        .await
        .expect_err("the reducer refuses to divide by zero");
    assert!(
        err.contains("Division by zero"),
        "A2: the consensus reducer raises a recoverable error, got {err:?}"
    );

    // The BigInt twin, unchanged — the two carriers now agree.
    let big = parse("1 / 0");
    assert_eq!(fold(&big).expect("the fold converges"), "error");

    // `%` by zero and the modulo-overflow corner share the disposition.
    assert_eq!(fold(&parse("int(1, 64) % int(0, 64)")).expect("the fold converges"), "error");
}

/// **Regression pin for the FABRICATION class itself (2026-07-25).**
///
/// The defect A/A2 recorded was not "the wrong number for overflow"; it was that a *checked*
/// operation, on failure, manufactured `Default::default()` and presented it as the answer. Every
/// arithmetic operator that could reach that emitter fallback is pinned here: none of them may
/// ever again produce a NUMBER for an operation that has no result.
#[tokio::test(flavor = "multi_thread")]
async fn no_arithmetic_failure_ever_fabricates_a_value() {
    for source in [
        // i64 overflow, every operator that can overflow.
        "int(9223372036854775807, 64) + int(1, 64)",
        "int(-9223372036854775808, 64) - int(1, 64)",
        "int(9223372036854775807, 64) * int(2, 64)",
        "-int(-9223372036854775808, 64)",
        // division and remainder by zero, both carriers.
        "int(1, 64) / int(0, 64)",
        "int(1, 64) % int(0, 64)",
        "1 / 0",
        "1 % 0",
        // u32 underflow / overflow (raw `u32` arithmetic PANICS, which aborts a fold here).
        "uint(0, 32) - uint(1, 32)",
        "uint(4294967295, 32) + uint(1, 32)",
        // ⚠ `float(1.0, 64) / float(0.0, 64)` was in this list. It has been MOVED OUT and is
        // asserted by `float_division_by_zero_answers_ieee754_not_the_error_term` instead. It was
        // never a member of this class: nothing was fabricated and nothing overflowed, and IEEE
        // 754 §7.3 gives `1.0 / 0.0` an ANSWER (`+Inf`). The comment that carried it here said
        // "`Inf - Inf` is NaN, which `SafeArith` declines", which describes a different
        // expression — `1.0 / 0.0` is not an indeterminate form. See the module header.
    ] {
        let folded = fold(&parse(source)).unwrap_or_else(|err| panic!("{source:?}: {err}"));
        assert_eq!(
            folded, "error",
            "{source:?} must fail CLOSED; a failed checked operation may never fabricate a value"
        );
    }
}

/// ★★ **Float ÷0 answers IEEE-754 — the same value upstream computes.** RULED 2026-07-29,
/// reversing the earlier same-day ruling that kept a refusal here.
///
/// | expression | f1r3node's `combine_div` (`GDouble` arm) | this fold |
/// |---|---|---|
/// | `1.0 / 0.0`  | `+Inf` | `+Inf` |
/// | `-1.0 / 0.0` | `-Inf` | `-Inf` |
/// | `0.0 / 0.0`  | `NaN`  | `NaN`  |
///
/// The floor is on SEMANTICS: a program upstream accepts must be accepted and must compute the
/// same value. IEEE 754 §7.3 defines all three, so the BUG-FIX carve-out does not apply and the
/// refusal was rejecting a program upstream runs.
///
/// ⚠ Each row is watched RED by the guard it replaces: restore the `y.get() == 0.0` guard and all
/// three rows report the `error` term. The `NaN` row is the sharp one — it is red both under the
/// old guard AND under any "just delete the guard" fix, because `SafeArith::safe_div` declines
/// `NaN` via `finite_or_inf_f64`, so the arm must bypass `SafeArith` rather than merely drop the
/// zero test.
///
/// ⚠ `-0.0` is deliberately NOT in the table. `CanonicalFloat64` canonicalises `-0.0` to `+0.0`
/// (`runtime/src/canonical_float.rs:35-42`) so that terms have a well-defined `Eq`/`Hash`/`Ord`, so
/// `1.0 / -0.0` answers `+Inf` here against upstream's `-Inf`. That is the CARRIER's divergence,
/// not division's; it is recorded in the module header and is out of this ruling's scope.
#[tokio::test(flavor = "multi_thread")]
async fn float_division_by_zero_answers_ieee754_not_the_error_term() {
    // FLOOR: a total float division still folds, so "the fold produced a float" below is not
    // satisfied by an evaluator that has stopped folding floats altogether.
    assert_eq!(
        fold(&parse("float(7.0, 64) / float(2.0, 64)")).expect("the fold converges"),
        "3.5",
        "★ FLOOR: ordinary float division must still compute",
    );

    for (source, expected) in [
        ("float(1.0, 64) / float(0.0, 64)", "inf"),
        ("float(-1.0, 64) / float(0.0, 64)", "-inf"),
        ("float(0.0, 64) / float(0.0, 64)", "NaN"),
    ] {
        let folded = fold(&parse(source)).unwrap_or_else(|err| panic!("{source:?}: {err}"));
        assert_eq!(
            folded, expected,
            "★★ {source:?} must answer the IEEE-754 value upstream computes, not the `error` term",
        );
    }

    // ⚠ `-0.0` — MEASURED, and pinned here so the CARRIER's divergence is a recorded fact rather
    // than a claim in prose. `CanonicalFloat64::canonicalize` maps `-0.0` to `+0.0`
    // (`runtime/src/canonical_float.rs:35-42`), and it does so at PARSE time: `float(-0.0, 64)`
    // parses to `FloatLit(0.0)`, not to a negated zero. So a signed zero is not a representable
    // `Float` TERM, and IEEE's sign rule for `x / -0.0` has no operand to act on.
    assert_eq!(
        fold(&parse("float(1.0, 64) / float(-0.0, 64)")).expect("the fold converges"),
        "inf",
        "★ `1.0 / -0.0` answers `+Inf` here where upstream answers `-Inf`, because `-0.0` \
         collapses to `+0.0` when the literal is built. That is `CanonicalFloat64`'s divergence, \
         not division's — the canonicalisation is what gives terms a well-defined `Eq`/`Hash`/`Ord` \
         — and it is out of the 2026-07-29 ruling's scope. If this ever reads `-inf`, the carrier \
         changed and the module header's residual-divergence note must be updated.",
    );
    assert_eq!(
        fold(&parse("float(-0.0, 64) / float(1.0, 64)")).expect("the fold converges"),
        "0.0",
        "★ and in the numerator: `-0.0 / 1.0` answers `+0.0`, where upstream preserves `-0.0`'s \
         bits — the same carrier-level collapse, observed from the other side",
    );
}

/// **Divergence A (target) — Rholang must INHERIT f1r3node's answer, never invent a third.**
///
/// This asserts only what is unambiguously MeTTaIL's to fix: the fold and the reducer must give
/// the *same* answer for the same expression in the same (process) position, whatever that answer
/// is. It is asserted *relatively* (`fold == reduce`), never absolutely.
///
/// ⚠ **Restated 2026-07-29.** The f1r3node-internal `reduce.rs` (`wrapping_add`) vs
/// `rho-pure-eval` (`checked_add`) question WAS an open upstream decision when this cell was
/// written; it has since been ruled — the reducer is now CHECKED and the two agree. What that
/// changes here is only the *shape* of the eventual agreement, not this cell's subject: the fold
/// answers the `error` TERM while the machine raises a recoverable `ReduceError`, so the
/// comparison below (`folded == render(value)`) still cannot be made until C1 deletes the
/// arithmetic fold bodies and leaves the machine as the only evaluator. Both sides now refuse
/// rather than one wrapping, which is why the residual gap is a REPRESENTATION difference and no
/// longer a value one.
///
/// Closed by **C1** (deleting the arithmetic fold bodies makes the machine the only evaluator).
#[tokio::test(flavor = "multi_thread")]
#[ignore = "divergence A: the fold answers the `error` TERM where the machine raises a \
            recoverable ReduceError — both refuse, but not in the same representation; \
            closed by C1 (delete the arithmetic fold bodies)"]
async fn divergence_a_target_int_overflow_inherits_the_f1r3node_evaluator() {
    for source in [
        "int(9223372036854775807, 64) + int(1, 64)",
        "int(-9223372036854775808, 64) - int(1, 64)",
    ] {
        let proc = parse(source);
        let folded = fold(&proc).expect("the fold converges");
        let observed = reduce(&proc).await.expect("the machine evaluates");
        let [value] = observed.as_slice() else {
            panic!("{source:?}: expected one observation, got {observed:?}");
        };
        assert_eq!(
            folded,
            render_as_rholang(value),
            "A: {source:?} — Rholang must inherit the f1r3node evaluator it routes to, \
             not contribute a third behaviour"
        );
    }
}

/// **Divergence A2 (target) — ★ CLOSED 2026-07-25.** `Int` division by zero must fail closed,
/// never answer `0`. The `#[ignore]` is removed: the emitter no longer has a fabricating fallback
/// for it to trip over.
#[tokio::test(flavor = "multi_thread")]
async fn divergence_a2_target_int_division_by_zero_fails_closed() {
    let proc = parse("int(1, 64) / int(0, 64)");
    let folded = fold(&proc).expect("the fold converges");
    assert_ne!(folded, "0", "A2: division by zero must never answer 0");
}

// ── B — `+` on a runtime-bound string ────────────────────────────────────────────────────────────

/// **Divergence B (witness) — `+`-on-strings is decided by STATIC shape on both sides, and the two
/// static decisions differ.**
///
/// Rholang's `EPlus` has no `GString` arm — `reduce.rs::combine_plus` (3100-3187) ends in
/// `OperatorNotDefined`; concatenation is `++` (`EPlusPlus`, `reduce.rs:2760-2775`). Rholang's
/// surface uses `+`, so `rholang-runtime/src/rholang_ast.rs:930-942` bridges the gap with a shim
/// that emits `EPlusPlus` **iff** `is_single_gstring_value` holds of the *already-lowered* operand
/// `Par`s (`rholang_ast.rs:1107-1121`) — a purely static test.
///
/// The `§17.11-B` inventory predicted that for a COMM-bound operand the FOLD would concatenate
/// while the machine errored. **Measurement partially refutes that.** For
/// `for (@s <- @("c")) { … "hello " + s … }`, `s` is a `Proc`-category variable, so the only
/// available reading of `+` is the `Proc`-level one; the fold fires the rendezvous and then leaves
/// the expression **unreduced**, resting as `@("OUT")!([@Nil!("hello ") + @Nil!("world")])`. So the
/// real divergence is:
///
/// | | statically ground operands | COMM-bound operand |
/// |---|---|---|
/// | fold ① | `"hello world"` | **silently unreduced** (a resting term, no error, no value) |
/// | reducer ② | `"hello world"` (via the shim ▸ `EPlusPlus`) | **`OperatorNotDefined`** — the whole reduction aborts |
///
/// Both sides fail to answer, with opposite failure modes: a silent resting term versus a hard
/// reduction error. That is still one operator with two meanings, and it is still decided by
/// static shape rather than by the value.
///
/// *Delete when C1 lands* (the fold body is gone, so `+`-on-strings means exactly one thing —
/// whatever Rholang means by it, per USER decision D-4).
#[tokio::test(flavor = "multi_thread")]
async fn divergence_b_witness_runtime_bound_string_add_diverges_by_static_shape() {
    let source = r#"@("c")!("world") | for (@s <- @("c")) { @("OUT")!("hello " + s) }"#;
    let proc = parse(source);

    // ① The fold fires the COMM and then rests with the `+` UNREDUCED — no error, no value.
    let folded = fold_program(&proc).expect("the COMM+fold fixpoint settles");
    assert!(
        folded.contains('+') && !folded.contains(r#""hello world""#),
        "B: the fold rests with an unreduced `+` rather than answering, got {folded:?}"
    );

    // ② The machine raises a hard reduction error instead.
    let err = reduce_program(&proc)
        .await
        .expect_err("Rholang's `+` has no GString arm");
    assert!(
        err.contains("OperatorNotDefined") && err.contains("string"),
        "B: the machine must raise OperatorNotDefined for `+` on a bound string, got {err:?}"
    );

    // Contrastive control: the STATICALLY ground twin is routed to `++` by the shim and BOTH
    // sides answer — so the divergence is exactly the dynamic case, not `+`-on-strings as such.
    let ground = parse(r#"@("OUT")!("hello " + "world")"#);
    assert_eq!(
        fold_program(&ground).expect("the ground twin folds"),
        // ★ SURFACE SYNONYMY (2026-07-26): the folded channel is `NQuote(CastStr("OUT"))`, and
        // Rholang's `Name` synonymy class `{ NQuote, NQuoteShort, NQuoteNil }` renders through
        // its DECLARED canonical member `NQuoteShort`, so the surface is the Rholang shorthand
        // `@"OUT"` rather than `@("OUT")`. The INPUT spelling above is unchanged and still
        // parses; only the rendered form moved, and it moved toward official Rholang, which
        // writes `@"OUT"!(…)`. What this control pins — that the STATICALLY ground twin folds
        // through the `++` shim while the runtime-bound one raises `OperatorNotDefined` — is
        // untouched. See `languages/tests/surface_synonymy_gate.rs`.
        r#"@"OUT"!("hello world")"#
    );
    let observed = reduce_program(&ground)
        .await
        .expect("the ground twin concatenates");
    assert_eq!(
        observed.iter().map(render_as_rholang).collect::<Vec<_>>(),
        vec![r#""hello world""#.to_string()]
    );
}

/// **Divergence B (target) — `+` on strings means ONE thing, decided by the value, not by what the
/// compiler happened to know.**
///
/// This asserts *position-independence* rather than a particular outcome, because the outcome is
/// USER decision **D-4** (§17.11.7): does Rholang conform *down* to Rholang — where `+` on strings
/// is simply undefined and `++` is concatenation — or is `+`-on-strings a deliberate Rholang-1.4
/// extension that must then work for bound operands too? Both answers satisfy this test; the
/// current ad-hoc static shim satisfies neither.
///
/// Note the asymmetry that makes the assertion meaningful: today the ground case answers and the
/// bound case does not, so `bound_behaves_like_ground` is false.
///
/// Closed by **C1**.
#[tokio::test(flavor = "multi_thread")]
#[ignore = "divergence B: the `Add`→`EPlusPlus` shim is a STATIC test, so `+` on a COMM-bound \
            string aborts the reduction while the ground twin concatenates; closed by C1"]
async fn divergence_b_target_string_add_is_position_independent() {
    let ground = reduce_program(&parse(r#"@("OUT")!("hello " + "world")"#)).await;
    let bound = reduce_program(&parse(
        r#"@("c")!("world") | for (@s <- @("c")) { @("OUT")!("hello " + s) }"#,
    ))
    .await;
    match (ground, bound) {
        (Ok(ground_values), Ok(bound_values)) => assert_eq!(
            ground_values
                .iter()
                .map(render_as_rholang)
                .collect::<Vec<_>>(),
            bound_values
                .iter()
                .map(render_as_rholang)
                .collect::<Vec<_>>(),
            "B: `+` on strings must not depend on when the operand became known"
        ),
        (Err(ground_err), Err(bound_err)) => assert_eq!(
            ground_err, bound_err,
            "B: if `+` on strings is undefined, it must be undefined in BOTH positions"
        ),
        (ground, bound) => panic!(
            "B: `+` on strings answers in one position and not the other \
             (ground: {ground:?}, bound: {bound:?})"
        ),
    }
}

// ── C — `nth` error discipline ───────────────────────────────────────────────────────────────────

/// **Divergence C (parts 1 + 2) — ★ CLOSED on the reducer-owned method path.**
///
/// The former `LNth` fold and its panic-prone host implementation no longer exist. Every spelling
/// below is the generic `MethodCall` constructor, lowers to `EMethod("nth")`, and is decided by
/// f1r3node's reducer. This pins both value and recoverable-error behavior without recreating a
/// second evaluator in the grammar.
#[tokio::test(flavor = "multi_thread")]
async fn divergence_c_closed_nth_is_total_and_carrier_agnostic() {
    // Out of range is a recoverable reducer error, never a host panic.
    for source in ["[1, 2, 3].nth(10)", "[1, 2, 3].nth(10u32)", "[].nth(0)"] {
        let error = reduce(&parse(source))
            .await
            .expect_err("out-of-range nth must fail recoverably");
        assert!(
            error.contains("index out of bound"),
            "C: {source:?} — expected the reducer's bounds error, got {error:?}",
        );
    }
    // Both direct surface spellings that lower to the reducer's GInt carrier agree. The
    // MeTTaIL-only `int(a, width)` fold is deliberately not smuggled into method-argument
    // evaluation now that methods have no host fold lane.
    for source in ["[1, 2, 3].nth(0)", "[1, 2, 3].nth(0u32)"] {
        assert_reducer_result(source, "1").await;
    }
    // A NON-integer index is refused by the same reducer method.
    let error = reduce(&parse(r#"[1, 2, 3].nth("0")"#))
        .await
        .expect_err("a string index must be rejected");
    assert!(
        error.contains("expression didn't evaluate to integer"),
        "C: expected a typed reducer refusal for a string index, got {error:?}",
    );

    // ★ CLOSED by C1 (2026-07-26). The tail that stood here asserted the lowering gap:
    //
    //     // ⚠ STILL OPEN: the machine never sees `nth` — the lowering rejects the construct.
    //     let err = reduce(&parse("[1, 2, 3].nth(0)"))
    //         .await
    //         .expect_err("the method is not lowered at all today");
    //     assert_eq!(err, "unsupported: l.nth(i) list method");
    //
    // `nth` now routes to `EMethod("nth")`, so the machine answers and the assertion that it
    // could not has moved to `divergence_c_target_nth_is_the_reducers_nth` — inverted, and live.
}

/// **★ Divergence C — FULLY CLOSED (C1, 2026-07-26). `nth` IS Rholang's `nth`.**
///
/// The FOLD half closed earlier (see [`divergence_c_closed_nth_is_total_and_carrier_agnostic`]);
/// the remaining half required the machine to be the one answering, and that is what **C1** did:
/// `EMethodBody(EMethod { method_name: "nth", … })` against the reducer's own method table
/// (`reduce.rs:9023` — MEASURED 2026-07-28; the ":8464" that stood here was stale).
///
/// ⚠ **THE TWO LANES DISAGREE OUT OF DOMAIN, AND THAT IS THE RULING, NOT A DEFECT.** For an
/// in-domain index the fold and the machine answer the same value. For an out-of-range index they
/// do not: the FOLD answers the `error` term (`v.get(n).cloned().unwrap_or(Proc::Err)`), while the
/// MACHINE raises the recoverable `ReduceError("Error: index out of bound: n")` asserted below.
/// The reducer's answer is the normative one — that is what routing MEANS — so the fold's `error`
/// is the MeTTaIL-side approximation of a condition the machine reports as a reduction error.
///
/// The consequence for any method that mirrors `nth`: "agrees with the fold" is a claim to be
/// checked WITHIN a lane (`[].last()` must answer what `[].nth(0)` answers **in the fold**, and
/// what `[].nth(0)` answers **on the machine**), never across the two.
#[tokio::test(flavor = "multi_thread")]
async fn divergence_c_target_nth_is_the_reducers_nth() {
    // A plain (BigInt) index works, on both sides.
    assert_reducer_result("[1, 2, 3].nth(0)", "1").await;
    assert_reducer_result("[1, 2, 3].nth(2)", "3").await;
    // Out of bounds is a RECOVERABLE error, never a panic.
    let err = reduce(&parse("[1, 2, 3].nth(10)"))
        .await
        .expect_err("out-of-bounds `nth` must be a recoverable reduction error");
    assert!(
        err.contains("index out of bound"),
        "C: expected Rholang's `index out of bound` error, got {err:?}"
    );
}

// ── `last` — routed 2026-07-28, and it EXECUTES ──────────────────────────────────────────────────
//
// ★ THE RED THESE REPLACED. Before `method_table` gained its `last` key, both tests below failed,
// and the failure was NOT "the value was wrong" — it was
//
//     unsupported: l.last() list method (no Rholang analog; C3 residue)
//
// raised by `rholang_ast.rs::unsupported_construct_name` BEFORE any Par reached the reducer. Three
// outcomes have to stay distinguishable and each has a different signature:
//
//   • "the read failed"        → the observation list is empty or the harness errors elsewhere;
//   • "it was never routed"    → `unsupported: …` (the LOWERING refused — the state before this
//                                change) or `reduce: … Unimplemented method: last` (the lowering
//                                emitted an `EMethod` the interpreter has no key for);
//   • "the value was wrong"    → the machine answers, and the answer is not the last element.
//
// The tests below assert an ANSWER, so the first two signatures fail them loudly, and the
// discriminator separates the third.

/// ★★ **`[1, 2, 3].last()` RUNS ON THE RHO MACHINE AND OBSERVES `3` — and `last` is not `first`.**
///
/// Not that it parses; not that a duplicate host evaluator can imitate it.
/// [`assert_reducer_result`] lowers the term, evaluates it on the real f1r3node reducer, and reads
/// the value resting on `@"OUT"`.
///
/// ⚠ **The discriminator is in this test on purpose.** `[111, 222, 333].last()` is `333` while the
/// **same list**'s `.nth(0)` is `111`. A `[1].last() == 1` assertion would pass under BOTH the
/// last-element and first-element readings and would assert nothing; keeping both halves in ONE
/// test means they cannot drift into separate files and separate fates.
#[tokio::test(flavor = "multi_thread")]
async fn last_executes_on_the_machine_and_is_not_the_first_element() {
    // The row that used to sit in `c3_residue_mettail_only_operations_fail_closed_and_named`
    // asserting the machine REFUSED this program. It now answers.
    assert_reducer_result("[1, 2, 3].last()", "3").await;

    // ★ The discriminator: head ≠ last, on the SAME list, both on the machine.
    assert_reducer_result("[111, 222, 333].last()", "333").await;
    assert_reducer_result("[111, 222, 333].nth(0)", "111").await;

    // …and stated as an inequality too, so the pair cannot be "fixed" by making both 333.
    let last = reduce(&parse("[111, 222, 333].last()"))
        .await
        .expect("`last` must execute on the machine");
    let head = reduce(&parse("[111, 222, 333].nth(0)"))
        .await
        .expect("`nth` executes on the machine");
    // MEASURED 2026-07-28 on the machine: `.last()` => `333`, `.nth(0)` => `111`.
    assert_ne!(
        render_as_rholang(&last[0]),
        render_as_rholang(&head[0]),
        "if `last` and `nth(0)` coincide on a 3-element list the fixture is vacuous"
    );
}

/// **`[].last()` on the machine, asserted BESIDE `[].nth(0)`.**
///
/// The two are compared for EQUALITY of the machine's error, not each matched against a pattern —
/// `last_method` computes `len - 1` with `saturating_sub` and hands `0` to the same `local_nth`
/// that `nth` calls, so on the empty list they are literally the same call and a divergence means
/// someone broke the sharing.
///
/// There is deliberately no host fold lane: `MethodCall` is a pure syntax constructor and the
/// reducer's recoverable error is the one normative answer.
#[tokio::test(flavor = "multi_thread")]
async fn last_on_the_empty_list_agrees_with_nth_zero_on_the_machine() {
    // ① the MACHINE lane: identical recoverable errors.
    let last_error = reduce(&parse("[].last()"))
        .await
        .expect_err("the empty list has no last element");
    let nth_error = reduce(&parse("[].nth(0)"))
        .await
        .expect_err("the empty list has no element 0 either");
    // MEASURED 2026-07-28 on the machine: both are, byte for byte,
    //     reduce: inj: ReduceError("Error: index out of bound: 0")
    assert_eq!(
        last_error, nth_error,
        "`[].last()` and `[].nth(0)` must be indistinguishable on the machine — they share \
         `local_nth`, so a difference here means the sharing was broken"
    );
    assert!(
        last_error.contains("index out of bound: 0"),
        "the empty-list answer must be the RECOVERABLE out-of-bounds error, never a panic and \
         never a silent value, got {last_error:?}"
    );
    // ★ Anti-vacuity: `expect_err` above would also be satisfied by the OLD lowering refusal, so
    // pin that the refusal is gone and the term really did reach the reducer.
    assert!(
        !last_error.starts_with("unsupported: "),
        "this must be the REDUCER's error, not the lowering's refusal — got {last_error:?}, \
         which is the pre-routing signature"
    );
}

// ── D — `Fixed` scale mismatch ───────────────────────────────────────────────────────────────────

/// **Divergence D (witness) — the fold rescales where the reducer refuses.**
///
/// `rholang/src/rust/interpreter/reduce.rs:3193-3200` requires `fp1.scale == fp2.scale` and
/// otherwise raises `OperatorExpectedError { expected: "FixedPoint(pN)" }`. Rholang's `Add` body
/// delegates to `CanonicalFixedPoint`'s `std::ops::Add`, which rescales to the wider scale, so
/// `1p0 + 0.5p1` folds to `1.5p1`.
///
/// *Delete when C1 lands.*
#[tokio::test(flavor = "multi_thread")]
async fn divergence_d_witness_fixed_scale_mismatch_rescales_in_the_fold() {
    let proc = parse("1p0 + 0.5p1");
    assert_eq!(
        fold(&proc).expect("the fold converges"),
        "1.5p1",
        "D: the fold rescales mismatched fixed-point operands"
    );
    let err = reduce(&proc)
        .await
        .expect_err("the reducer rejects mismatched scales");
    assert!(
        err.contains("OperatorExpectedError") && err.contains("FixedPoint"),
        "D: expected reduce.rs's scale-equality precondition, got {err:?}"
    );
}

/// **Divergence D (target) — one fixed-point scale policy, the reducer's.**
///
/// Closed by **C1**.
#[tokio::test(flavor = "multi_thread")]
#[ignore = "divergence D: `1p0 + 0.5p1` rescales in the fold and is rejected by reduce.rs:3193; \
            closed by C1"]
async fn divergence_d_target_fixed_scale_policy_is_the_reducers() {
    let proc = parse("1p0 + 0.5p1");
    let folded = fold(&proc).expect("the fold converges (to a value or to `error`)");
    match reduce(&proc).await {
        // The reducer answered ⇒ the fold must answer the same value.
        Ok(values) => {
            let [value] = values.as_slice() else {
                panic!("D: expected one observation, got {values:?}");
            };
            assert_eq!(
                folded,
                render_as_rholang(value),
                "D: the fold must adopt the reducer's fixed-point scale policy"
            );
        },
        // The reducer refused ⇒ the fold must refuse too, never silently rescale.
        Err(err) => assert_eq!(
            folded, "error",
            "D: the reducer refused ({err}), so the fold must fail closed rather than rescale"
        ),
    }
}

// ── E / F — the forked wire schema and `.toByteArray()` ──────────────────────────────────────────

/// **Divergences E + F — CLOSED by C2 (2026-07-25).**
///
/// `.toByteArray()` is now f1r3node's own `toByteArray`: the lowering emits
/// `EMethod("toByteArray")` (`rholang-runtime/src/rholang_ast.rs::lower_method`) and the reducer
/// evaluates it (`reduce.rs:4137-4160` — `eval_expr` + `substitute`, then `p.encode_to_vec()`),
/// returning a real `GByteArray`.
///
/// ### What was retired, and why the goldens changed
///
/// `languages/src/rholang/wire.rs` + `languages/proto/rholang_wire.proto` + `languages/build.rs`
/// were a hand-maintained **fork** of f1r3node's `rhoapi` schema (7 of its 62 messages), compiled
/// by `protoc` into a *second* `rhoapi::Par` type in the same workspace. Three independent defects
/// made it unsalvageable rather than merely redundant:
///
/// | # | Defect | Consequence |
/// |---|---|---|
/// | 1 | the fork's `.proto` had **no `g_big_int` field**, and `proc_to_par` matched only `Proc::CastInt(Int::NumLit(_))` | a plain Rholang integer literal is arbitrary-precision (`CastBigInt`), so `.toByteArray()` folded to `error` for every collection the grammar produces |
/// | 2 | it sorted set/map members by raw **protobuf byte order** (`wire.rs:19-25`, `sort_by_key(encode_to_vec)`) | disagrees with Rholang's **`ScoredTerm` value order** (`models/src/rust/sorted_par_hash_set.rs:22`) on negative integers — divergence **E** |
/// | 3 | it returned a **hex `GString`**, not a `GByteArray` (`wire.rs:136-139`) | the wrong Rholang carrier — divergence **F** |
///
/// ### ★ RE-MEASURED 2026-07-25 after divergence I closed
///
/// The C2 goldens were re-baselined onto `GBigInt` leaves (`9a 02 01 0N`) because a plain Rholang
/// numeral was then a `CastBigInt`. **It should never have been**: `normalize_ground` maps a bare
/// numeral to `GInt`, and divergence I fixed the grammar accordingly. So these goldens are measured
/// again, deliberately — a carrier change moves the wire bytes, and rubber-stamping them would have
/// hidden exactly the thing this suite exists to catch.
///
/// The new bytes for `[1,2,3]`, `2a15a201120a042a0210020a042a0210040a042a021006`, are **byte-
/// identical to the goldens the RETIRED FORK produced** (`GInt` elements, `sint64` zigzag
/// `02 04 06` = 1, 2, 3). That is a receipt, not a coincidence: defect #1 in the table above was
/// that the fork's `.proto` had no `g_big_int` field — the fork was encoding what Rholang actually
/// means, and only *looked* wrong because Rholang's literals were landing in the wrong carrier.
/// The `GBigInt` encoding is now reached by exactly the spelling that asks for it, `[1n, 2n, 3n]`
/// (pinned below).
///
/// (The five golden-hex tests that pinned the fork lived in
/// `languages/tests/rholang_tests.rs::native_ops::collection_wire`. They were retired rather than
/// migrated because they asserted nothing: see that module's replacement comment for the measured
/// `assert_reduces_to` vacuity.)
#[tokio::test(flavor = "multi_thread")]
async fn c2_closed_to_byte_array_is_the_reducers_own_encoding() {
    for (source, expected) in [
        // A list of three PLAIN integers: `EList` (field 20 ⟹ `a2 01`) of three `Par`s each
        // carrying one `GInt` (`2a 02 10`) leaf, `sint64` zigzag `02 04 06` = 1, 2, 3.
        ("[1, 2, 3].toByteArray()", "2a15a201120a042a0210020a042a0210040a042a021006"),
        // The `…n` spelling — and ONLY it — reaches `GBigInt` (`9a 02`).
        (
            "[1n, 2n, 3n].toByteArray()",
            "2a1ba201180a062a049a0201010a062a049a0201020a062a049a020103",
        ),
        // `ESet` (field 22 ⟹ `b2 01`). Source order is irrelevant — the machine canonicalizes
        // through `SortedParHashSet`, so both spellings give byte-identical output.
        ("Set(1, 2, 3).toByteArray()", "2a15b201120a042a0210020a042a0210040a042a021006"),
        ("Set(3, 2, 1).toByteArray()", "2a15b201120a042a0210020a042a0210040a042a021006"),
        // `EMap` (field 23 ⟹ `ba 01`), likewise order-independent.
        (
            "{1: 10, 2: 20}.toByteArray()",
            "2a1fba011c0a0c0a042a02100212042a0210140a0c0a042a02100412042a021028",
        ),
        (
            "{2: 20, 1: 10}.toByteArray()",
            "2a1fba011c0a0c0a042a02100212042a0210140a0c0a042a02100412042a021028",
        ),
        // Nesting rides through unchanged.
        (
            "[[1, 2], [3]].toByteArray()",
            "2a23a201200a112a0fa2010c0a042a0210020a042a0210040a0b2a09a201060a042a021006",
        ),
        // The empty list — the one case the retired fork also got right, since it has no elements
        // to mis-type. Byte-identical across every re-baseline: `2a03a20100`.
        ("[].toByteArray()", "2a03a20100"),
    ] {
        let observed = reduce(&parse(source))
            .await
            .unwrap_or_else(|err| panic!("{source:?}: the machine must own toByteArray: {err}"));
        let [RuntimeObservationValue::Bytes(bytes)] = observed.as_slice() else {
            panic!("{source:?}: `toByteArray` must return a GByteArray, got {observed:?}");
        };
        assert_eq!(hex_of(bytes), expected, "{source:?}");
    }
}

/// **E3 — byte methods are evaluated only by f1r3node's method table.**
///
/// These rows replace the retired host folds. They pin the byte carrier, unsigned indexing,
/// canonical hex rendering, UTF-8 conversion, and upstream's deliberately permissive
/// filter-and-left-pad hex decoder through the production lowering/reducer path.
#[tokio::test(flavor = "multi_thread")]
async fn e3_byte_methods_are_owned_by_the_reducer() {
    for (source, expected) in [
        (r#"b"dead".length()"#, "2"),
        (r#"b"deadbeef".nth(1)"#, "173"),
        (r#"b"deadbeef".last()"#, "239"),
        (r#"b"80".nth(0)"#, "128"),
        (r#"b"000f".bytesToHex()"#, r#""000f""#),
    ] {
        assert_reducer_result(source, expected).await;
    }

    for (source, expected) in [
        (r#""deadbeef".hexToBytes()"#, vec![0xde, 0xad, 0xbe, 0xef]),
        // Match the reducer's Scala-compatible decoder: filter non-hex characters, then
        // left-pad an odd digit count.
        (r#""abc".hexToBytes()"#, vec![0x0a, 0xbc]),
        (r#""de-ad".hexToBytes()"#, vec![0xde, 0xad]),
        (r#""hello world".hexToBytes()"#, vec![0xed]),
        (r#""dead".toUtf8Bytes()"#, b"dead".to_vec()),
        (r#""λ".toUtf8Bytes()"#, "λ".as_bytes().to_vec()),
    ] {
        let observed = reduce(&parse(source))
            .await
            .unwrap_or_else(|error| panic!("{source:?}: reducer byte method failed: {error}"));
        assert_eq!(
            observed,
            vec![RuntimeObservationValue::Bytes(expected)],
            "{source:?}: byte result drifted",
        );
    }

    for source in [r#"b"dead".hexToBytes()"#, r#""dead".bytesToHex()"#] {
        let error = reduce(&parse(source))
            .await
            .expect_err("a known method on the wrong carrier must fail closed");
        assert!(
            error.contains("MethodNotDefined"),
            "{source:?}: expected the reducer's carrier diagnostic, got {error:?}",
        );
    }
}

/// **Divergence E — CLOSED by C2: the canonical order is the machine's, not protobuf byte order.**
///
/// `Set(0 - 2, 1)` is the discriminating case, and ★ RE-MEASURED 2026-07-25: it now lands on
/// Rholang's `ScoredTerm` **value** order, `-2` before `1`.
///
/// That is a second-order effect of divergence I, and it is worth stating precisely. While a plain
/// numeral was a `CastBigInt`, the members rode as `GBigInt` — which `ScoredTerm` scores on its
/// signed big-endian **bytes**, so `01` (=1) sorted before `fe` (=-2) and the *observed* order was
/// `1, -2`, agreeing with neither the value order nor with intuition. With the members now riding
/// as `GInt` (their `normalize_ground` carrier) the machine scores them by value and answers
/// `-2, 1`. Either way there is exactly ONE implementation of the order — the machine's
/// `SortedParHashSet` — rather than a second, independently-sorted host encoder; that is what C2
/// closed. What divergence I added is that the one implementation is now fed the right carrier.
#[tokio::test(flavor = "multi_thread")]
async fn c2_closed_to_byte_array_uses_the_machines_canonical_order() {
    let observed = reduce(&parse("Set(0 - 2, 1).toByteArray()"))
        .await
        .expect("E: the machine encodes a set with a negative member");
    let [RuntimeObservationValue::Bytes(bytes)] = observed.as_slice() else {
        panic!("E: expected a GByteArray, got {observed:?}");
    };
    assert_eq!(
        hex_of(bytes),
        // `b2 01` ESet of two `GInt` leaves: zigzag `03` = -2, then zigzag `02` = 1.
        "2a0fb2010c0a042a0210030a042a021002",
        "E: the member order is the machine's own — by VALUE, `-2` then `1`"
    );
}

/// **The `Bag` carrier survives `.toByteArray()` — a C2 side-benefit worth pinning.**
///
/// `Bag` is a MeTTaIL-only category (no Rholang analog), so `lower_bag`
/// (`rholang-runtime/src/rholang_ast.rs`) represents it as an `EList` tagged with
/// `RHOLANG_BAG_ABI_TAG` (`mettail.rholang.bag.v1`, visible in the bytes below) carrying
/// `(element, count)` pairs. The retired fork instead **expanded the multiset** into a bare
/// `EList` of repeated elements, discarding both the tag and the count structure — so its bytes
/// decoded back to a *list*, not a bag. Routing through `EMethod` means the bytes are the encoding
/// of the term Rholang actually lowers.
#[tokio::test(flavor = "multi_thread")]
async fn c2_closed_bag_to_byte_array_keeps_the_bag_abi_tag() {
    let observed = reduce(&parse("#{1 | 2 | 2}#.toByteArray()"))
        .await
        .expect("the machine encodes the lowered bag");
    let [RuntimeObservationValue::Bytes(bytes)] = observed.as_slice() else {
        panic!("expected a GByteArray, got {observed:?}");
    };
    let encoded = hex_of(bytes);
    assert!(
        encoded.contains(&hex_of(RHOLANG_BAG_ABI_TAG.as_bytes())),
        "the bag ABI tag must ride the encoding, got {encoded}"
    );
    assert_eq!(
        encoded,
        // ★ RE-MEASURED 2026-07-25 (divergence I): the ELEMENT leaves are now `GInt` (`2a 02 10`)
        // rather than `GBigInt` (`9a 02`); the `(element, count)` pair structure and the ABI tag
        // are unchanged. The counts were always `GInt`, so each pair is now homogeneous.
        //
        // ★ RE-PINNED 2026-07-27 (task #22, the `rholang` → `rholang` rename): the tag bytes
        // `72686f63616c63` ("rholang") became `72686f6c616e67` ("rholang"). This is the ONLY
        // byte-level site of the ABI tag — textual substitution reaches the constant and the
        // `&str` literal but not a hex TRANSCRIPT of them, so this line is hand-re-pinned. The
        // two names are both 7 bytes, so every surrounding protobuf length prefix is unchanged
        // and the rest of the encoding is byte-identical to the 2026-07-25 measurement.
        "2a50a2014d0a1e3a1c0a1a0a180a166d65747461696c2e72686f6c616e672e6261672e76310a2b2a29\
         a201260a112a0fa2010c0a042a0210020a042a0210020a112a0fa2010c0a042a0210040a042a021004"
    );
}

// ── G — Pathmap and zipper carriers ──────────────────────────────────────────────────────────────

/// **Divergence G — ★ CLOSED 2026-08-01.**
///
/// A Rholang pathmap now lowers directly to the homogeneous native carrier:
/// set literals select `PathMap<()>`, map literals select `PathMap<Par>`, and an
/// empty literal stays neutral until its first typed insertion.  Generic map
/// methods and zipper methods both dispatch on `EPathmapBody`; no `EMap`
/// compatibility encoding or decoded entry vector sits on either route.
///
/// `RuntimeObservationValue` intentionally has no pathmap/zipper variant, so
/// this closure test observes operations *through* the carrier: value lookup
/// proves the map specialization survived, and `leafCount` proves the zipper
/// sees the same trie.
#[tokio::test(flavor = "multi_thread")]
async fn divergence_g_closed_pathmaps_and_zippers_use_native_homogeneous_tries() {
    assert_eq!(fold(&parse("{|1:2|}")).expect("the fold converges"), "{|1:2|}");

    let observed = reduce(&parse("{|1:2|}.get(1)"))
        .await
        .expect("map lookup reaches PathMap<Par>");
    assert_eq!(
        observed.iter().map(render_as_rholang).collect::<Vec<_>>(),
        vec!["2".to_string()]
    );

    let observed = reduce(&parse("{|1:2|}.readZipper().leafCount()"))
        .await
        .expect("zipper construction reaches the native trie");
    assert_eq!(
        observed.iter().map(render_as_rholang).collect::<Vec<_>>(),
        vec!["1".to_string()]
    );
}

// ── H — boolean equality (discovered by this suite) ──────────────────────────────────────────────

/// **Divergence H — ★ CLOSED 2026-07-25.**
///
/// H was discovered by this suite: `languages/src/rholang.rs`'s `Eq`/`Ne` fold bodies had arms for
/// every ground type EXCEPT `Bool`, so `true == true` fell through to the collection-equality
/// fallback and answered `Proc::Err`, while the machine answered `true`.
///
/// Rholang is normative and Rholang's `==` is STRUCTURAL equality on the whole `Par`
/// (`reduce.rs::combine_eq`, `sv1 == sv2` after substitution — not `relopb`, which serves only
/// `<`/`<=`/`>`/`>=`), so two `GBool`s compare by value. Rholang now has the matching `Bool` arm
/// in both `Eq` and `Ne`, and its target twin
/// [`divergence_h_target_boolean_equality_agrees`] is GREEN.
///
/// This test keeps the FOLD side pinned so the arm cannot be lost again.
#[tokio::test(flavor = "multi_thread")]
async fn divergence_h_closed_boolean_equality_folds_to_a_boolean() {
    for (source, answer) in [
        ("true == true", "true"),
        ("true != false", "true"),
        ("true == false", "false"),
        ("false != false", "false"),
    ] {
        assert_eq!(
            fold(&parse(source)).expect("the fold converges"),
            answer,
            "H: {source:?} — the fold decides boolean equality by value, as `combine_eq` does"
        );
    }
}

/// **Divergence H (target) — boolean equality agrees. ★ CLOSED 2026-07-25** (the `#[ignore]` is
/// removed).
#[tokio::test(flavor = "multi_thread")]
async fn divergence_h_target_boolean_equality_agrees() {
    assert_conformant("true == true", "true").await;
    assert_conformant("true != false", "true").await;
    assert_conformant("true == false", "false").await;
}

// ── I — the numeric-literal CARRIER depends on syntax (discovered 2026-07-25) ─────────────────────

/// **Divergence I — ★ CLOSED 2026-07-25 in the GRAMMAR (`languages/src/rholang.rs`).**
///
/// Rholang has ONE integer type. MeTTaIL offers several carriers for it (`Int` = `i64` ▸ `GInt`,
/// `BigInt` = arbitrary precision ▸ `GBigInt`, `UInt32`), which is fine as long as the carrier is
/// a function of the SOURCE. It was not. The retired witness recorded:
///
/// | source | parsed | carrier |
/// |---|---|---|
/// | `*(@1) + 2` | `Add(PDrop(NParen(NQuoteShort(CastBigInt(1)))), CastBigInt(2))` | both arbitrary precision |
/// | `*(@(1)) + 2` | `Add(PDrop(NParen(NQuoteShort(**CastInt**(1)))), CastBigInt(2))` | MIXED |
/// | `5u32` | `CastBigInt(5)` | the `u32` suffix reached no `UInt32` |
///
/// Both this grammar's operators and the consensus reducer are carrier-EXACT, so the asymmetry was
/// a semantic difference: one pair of parentheses turned `3` into `error`, and `[1,2,3].length() ==
/// 3` was false (a computed length is an `Int`; a literal `3` was a `BigInt`).
///
/// ### The attribution was HALF WRONG, and that is the lesson
///
/// The witness said "the fix belongs in the WPDA cross-category projection". The election machinery
/// behaved exactly as specified — what it was electing *between* was a set of readings **the
/// grammar should never have admitted**: `BigInt`'s eval was `parse_int_lit(text, None)`, a
/// universal acceptor of every integer spelling, flatly contradicting its own declared mandatory
/// `…n` tail. Respecting never-disambiguate-early did NOT require touching the tiebreak; it
/// required making the evidence discriminate. Once the literal domains PARTITION, exactly one
/// carrier survives at every election site and no ledger argument is needed at all.
///
/// The normative source settles which carrier: f1r3node's `normalize_ground`
/// (`ground_normalize_matcher.rs:14-50`) maps a bare numeral, `…i32`, `…i64` and `…u32` (≤
/// `i64::MAX`) to `GInt`, and only `…n` to `GBigInt`.
///
/// The MeTTaIL-side pins are `languages/tests/rholang_tests.rs::numeral_carrier_is_context_
/// independent`.
#[tokio::test(flavor = "multi_thread")]
async fn divergence_i_closed_numeral_carrier_is_syntax_independent() {
    assert_conformant("int(1, 64) + 2", "3").await;
    // (`5u32 bitand 3u32` is pinned on the MeTTaIL side only — `bitand` is a MeTTaIL-only
    // operation with no Rholang `Expr`, so it is C3 residue and cannot be asserted CONFORMANT.
    // Its carrier claim lives in `languages/tests/rholang_tests.rs::
    // numeral_carrier_is_context_independent::u32_suffix_is_an_i64_literal`.)
    assert_conformant("5u32 + 3u32", "8").await;
    // The parenthesis witness itself: one pair of parentheses used to change the carrier.
    assert_conformant("*(@1) + 2", "3").await;
    assert_conformant("*(@(1)) + 2", "3").await;
    // The computed-vs-literal witness. The reducer owns `.length()` and the surrounding equality;
    // this proves the computed and literal integers share one machine carrier.
    assert_reducer_result("[1, 2, 3].length() == 3", "true").await;
}

/// **The f1r3node fact divergence I rested on, kept as a standalone pin.**
///
/// The retired witness ended by asserting it, and it is the reason the grammar-side fix had to make
/// the carriers agree rather than teach the fold to mix them: the consensus reducer's `combine_plus`
/// (`reduce.rs:3112`) has **no mixed `GInt`/`GBigInt` arm**. MeTTaIL cannot be more permissive than
/// the machine it compiles to, so a mixed-carrier addition must stay refused on BOTH sides — and the
/// only conforming way to make `1 + 2` compute is for both operands to be the SAME carrier.
///
/// (Recorded, not requested: whether f1r3node should grow such an arm is an upstream question. No
/// f1r3node change was made for divergence I.)
#[tokio::test(flavor = "multi_thread")]
async fn f1r3node_combine_plus_has_no_mixed_gint_gbigint_arm() {
    let mixed = parse("int(1, 64) + 2n");
    assert_eq!(
        fold(&mixed).expect("the fold converges"),
        "error",
        "the fold's `+` is carrier-exact"
    );
    let machine = reduce(&mixed).await;
    assert!(
        machine.is_err(),
        "the consensus reducer's `combine_plus` (reduce.rs:3112) has no mixed \
         `GInt`/`GBigInt` arm either — got {machine:?}"
    );
    // …and each carrier on its own computes, on both evaluators, so the refusal above is about
    // MIXING and not about either carrier being broken.
    assert_conformant("int(1, 64) + int(2, 64)", "3").await;
    assert_conformant("1n + 2n", "3n").await;
    assert_conformant("1 + 2", "3").await;
}

// ── J — an EMPTY send satisfies an arity-1 receive (discovered 2026-07-25) ────────────────────────

/// **Divergence J (witness) — `x!()` fires against `for(@y <- x)` and delivers the empty list.**
///
/// Rholang canonicalizes every send payload to a LIST (`x!(p)` ≡ `x!([p])`, `x!()` ≡ `x!([])` —
/// pinned by `languages/tests/rholang_tests.rs::parsing::{send_unary_is_list_sugar,
/// send_empty_is_list_sugar}`), and a whole-message binder receives that payload. So the 0-arity
/// send `x!()` satisfies the 1-arity receive `for(@y <- x)` and binds `y = []`.
///
/// Rholang's COMM is ARITY-CHECKED: `x!()` produces a `Send` with an empty `data` vector, and a
/// `Receive` whose single `ReceiveBind` has one pattern never matches it, so the program rests.
/// (Rholang agrees for multi-binder rows — `x!(1,2) | for(a,b,c <- x){…}` blocks — so the
/// divergence is specific to the whole-message binder against the EMPTY payload.)
///
/// Discovered while burning down `languages/tests/rholang_tests.rs`, where
/// `send_empty_payload_quoted_bind_emits_empty_proc` had an expectation that contradicted both its
/// own name and the sugar pins, and only "passed" because `assert_reduces_to` was vacuous.
#[tokio::test(flavor = "multi_thread")]
async fn divergence_j_witness_empty_send_satisfies_an_arity_one_receive() {
    assert_eq!(
        fold_program(&parse("for(@y <- x){y} | x!()")).expect("the fold fixpoint settles"),
        "{[]}",
        "J: the empty send's payload IS `[]`, and the whole-message binder receives it"
    );
    // The multi-binder row is arity-checked, so the divergence is not "Rholang ignores arity".
    let blocked = fold_program(&parse("x!(1,2) | for(a, b, c <- x){[a,b,c]}"))
        .expect("the fold fixpoint settles");
    assert!(
        blocked.contains("for("),
        "J: a polyadic arity mismatch DOES block, got {blocked:?}"
    );
}

/// **Divergence J (target) — the empty send does not satisfy an arity-1 receive.**
///
/// Closed by making the fold's COMM arity-check the whole-message binder the way Rholang's
/// `ReceiveBind` does (or by C1, which deletes the fold's COMM entirely).
#[tokio::test(flavor = "multi_thread")]
#[ignore = "divergence J: `for(@y <- x){y} | x!()` fires and yields `[]`; Rholang's arity-checked \
            COMM leaves it at rest"]
async fn divergence_j_target_empty_send_does_not_satisfy_an_arity_one_receive() {
    let source = "for(@y <- x){y} | x!()";
    let folded = fold_program(&parse(source)).expect("the fold fixpoint settles");
    assert!(folded.contains("for("), "J: the receive must still be waiting, got {folded:?}");
}

// ════════════════════════════════════════════════════════════════════════════════════════════════
// PART 3 — the MeTTaIL-only residue (C3): operations Rholang has NO analog for
//
// These must keep exactly ONE implementation. Today it is the fold body, and the machine rejects
// them fail-closed; C3 injects that one implementation as a system-process `Definition` reusing
// the proven `rholang-runtime/src/fold_contract.rs` pattern (`HeldFoldContractSound.v`), so the
// residue is available on the machine WITHOUT a second implementation ever existing.
// ════════════════════════════════════════════════════════════════════════════════════════════════

/// The MeTTaIL-only operations, pinned as fail-closed on the machine with a *named* construct.
/// The naming is the contract: nothing silently host-evaluates
/// (`rholang-runtime/src/rholang_ast.rs::unsupported_construct_name`).
///
/// *Amend when C3 lands:* each of these becomes a system-process `Definition` invocation, so the
/// machine answers instead of rejecting — but the answer still comes from the SAME single Rust
/// implementation the fold used.
#[tokio::test(flavor = "multi_thread")]
async fn c3_residue_mettail_only_operations_fail_closed_and_named() {
    for (source, fold_answer, machine_error) in [
        // ★ GOLDEN RE-DERIVED, NOT RELAXED (2026-07-26). This read `"1/2"` and had been red since
        // `98d861a3` gave `BigRat`'s token pattern the leading `-?` that mirrors consensus
        // Rholang's `bigrat_literal /-?\d+r/`. `mandatory_literal_tail_of_pattern`
        // (`macros/src/gen/syntax/display.rs`) grants a mandatory literal tail only when the
        // pattern's language covers EVERY value the native type can render, and its sign
        // side-condition — *"a signed payload renders a leading `-`, so a pattern that does not
        // accept one cannot be given a tail"* — was the ONLY reason `BigRat` had no `r` tail while
        // `BigInt` has had its `n` tail since Stage C. With `-?` in place the tail is emitted, so a
        // rational renders `1/2r`. `98d861a3` re-baselined the three `rholang_tests.rs` goldens
        // this moved and MISSED this fourth one, in a different file.
        //
        // ★ RE-DERIVED A SECOND TIME (2026-07-27), and the asymmetry the note below recorded is
        // now CLOSED. `98d861a3` left `BigRat` able to render a word it could not read back: the
        // `r` tail was appended to `Ratio`'s own `n/d` rendering, so `1/2r` re-parsed as
        // `Div(CastInt(1), CastBigRat(2))` rather than as the composite rational, and `1r/2r` —
        // the only spelling of the composite value — was a hard parse error. D2
        // (`ab13aee0`, *"a literal category must be able to spell every value it can hold"*)
        // widened `BigRat`'s pattern with `(/(…)r)?`, and the already-grammar-derived composite
        // arm then WRITES the spelling it can read: `fraction(1, 2)` ⇒ `1r/2r`.
        //
        // ⚠ That commit re-baselined the three `rholang_tests.rs` goldens the change moved and,
        // exactly as `98d861a3` did before it, MISSED this fourth one in a different file. The
        // golden is updated, NOT relaxed — `1r/2r` is the surface that round-trips.
        ("fraction(1, 2)", "1r/2r", "unsupported: fraction(a, b) rational constructor"),
        // `reduce.rs::method_table` provides `keys` but NOT `values` — a Map's values are
        // reachable in Rholang only via `toList`/`get`. So `.values()` is a Rholang extension
        // with no Rholang counterpart, and it stays MeTTaIL-only under C3.
        (
            "{1 : 10}.values()",
            "{1:10}.values()",
            r#"reduce: inj: ReduceError("Unimplemented method: values")"#,
        ),
        // ★★ `.last()` WAS PINNED HERE AS RESIDUE, AND HAS MOVED OUT DELIBERATELY (2026-07-28).
        //
        // Two rows stood here — `[1, 2, 3].last()` and `[].last()` — each asserting the machine
        // refused with `"unsupported: l.last() list method (no Rholang analog; C3 residue)"`.
        // They were correct while `method_table` had no `last` key. It now has one
        // (`reduce.rs::last_method`), so `last` ROUTES, the machine ANSWERS, and residue rows for
        // it would be false. They were not deleted quietly: both moved to
        // [`last_executes_on_the_machine_and_is_not_the_first_element`] and
        // [`last_on_the_empty_list_agrees_with_nth_zero_on_the_machine`], where the same two
        // programs are asserted against the machine's ANSWER instead of its refusal.
        //
        // A green suite must not be able to hide that transition, which is why the move is
        // recorded here rather than left as an absence.
        ("5 bitand 3", "1", "unsupported: bitand bitwise-and (no Rholang bitwise Expr)"),
        ("bool(1p0)", "true", "unsupported: bool(a) boolean conversion"),
        (r#"str(1.5p1)"#, r#""1.5p1""#, "unsupported: str(a) string conversion"),
    ] {
        let proc = parse(source);
        assert_eq!(
            fold(&proc).expect("the fold converges"),
            fold_answer,
            "C3: {source:?} — the single MeTTaIL-side implementation"
        );
        assert_eq!(
            reduce(&proc).await.expect_err("no Rholang analog exists"),
            machine_error,
            "C3: {source:?} — the machine must fail closed, NAMING the construct"
        );
    }
}

// ════════════════════════════════════════════════════════════════════════════════════════════════
// PART 4 — the C1 work list: every collection method the machine cannot see today
// ════════════════════════════════════════════════════════════════════════════════════════════════

/// **★ The `Bag` ENCODING is rejected by every routed method that could see it — MEASURED.**
///
/// This test exists because the design note that held C1 back asserted the opposite. It claimed
/// that routing would make `#{1|2|2}#.size()` "answer the tagged list's pair count instead of the
/// multiset cardinality — a SILENTLY WRONG answer". Measured 2026-07-26, that is **false**:
/// `size_method` (`reduce.rs:7829`) accepts only `EMapBody`/`ESetBody`, so the lowered bag —
/// `EList[GPrivate(RHOLANG_BAG_ABI_TAG), EList[pairs]]` — is refused by name and type.
///
/// The hazard the note was reaching for is real, but it lives on the two routed methods that DO
/// accept `EListBody` (`length`, `nth`), and those are gated at the lowering; see
/// [`c1_bag_length_and_nth_are_gated_at_lowering`] and the residue witness
/// [`c1_bag_length_residue_when_the_carrier_is_only_known_at_runtime`].
///
/// The former host method folds have been deleted. The machine must fail CLOSED — never answer
/// about the encoding — and this test now observes only the reducer-owned method path.
#[tokio::test(flavor = "multi_thread")]
async fn c1_bag_encoding_is_rejected_by_every_routed_method() {
    for (source, machine_error) in [
        (
            "#{1 | 2 | 2}#.size()",
            r#"reduce: inj: MethodNotDefined { method: "size", other_type: "list" }"#,
        ),
        (
            "#{1 | 2 | 2}#.union(#{3}#)",
            r#"reduce: inj: MethodNotDefined { method: "union", other_type: "list" }"#,
        ),
        (
            "#{1 | 2 | 2}#.diff(#{2}#)",
            r#"reduce: inj: MethodNotDefined { method: "diff", other_type: "list" }"#,
        ),
    ] {
        let proc = parse(source);
        assert_eq!(
            reduce(&proc)
                .await
                .expect_err("the bag encoding must be refused"),
            machine_error,
            "C1: {source:?} — the machine must REFUSE the bag encoding, not measure it"
        );
    }
}

/// **`length`, `nth`, and `last` are gated at lowering, because the reducer WOULD answer.**
///
/// These are exactly the routed operations whose interpreter implementation accepts `EListBody`,
/// and therefore exactly the ones that could measure the 2-element bag ABI encoding and return
/// something plausible instead of failing:
///
/// | operation | interpreter | accepts `EList`? | ungated answer for a bag |
/// |---|---|---|---|
/// | `length` | `length_method` (7893) | **yes** | `2` — tag + pairs — not the cardinality `3` |
/// | `nth` | `nth_method` (4078) | **yes** | the ABI tag, or the pairs list |
/// | `last` | `last_method` (4449) | **yes** | the PAIRS LIST — the encoding's 2nd element |
///
/// ⚠ The `last` row was added on 2026-07-28 when `last` became routed. Routing an operation that
/// accepts `EListBody` ADDS a way to measure the bag ABI encoding, so the gate had to grow with
/// it; a routed `last` without the gate would answer `#{…}#.last()` with the encoding's pairs
/// list, which is plausible and wrong.
///
/// Every other routed method accepts only `EMapBody`/`ESetBody`/`EPathmapBody` and so refuses the
/// encoding by itself — measured in [`c1_bag_encoding_is_rejected_by_every_routed_method`]. The
/// gate ([`receiver_is_literal_bag`] in `rholang_ast.rs`) covers the case decidable at lowering
/// time. `concat` has no reducer method and therefore fails closed as an unimplemented name.
#[tokio::test(flavor = "multi_thread")]
async fn c1_bag_length_and_nth_are_gated_at_lowering() {
    for source in ["#{1 | 2 | 2}#.length()", "#{1 | 2 | 2}#.nth(0)", "#{1 | 2 | 2}#.last()"] {
        let proc = parse(source);
        let error = reduce(&proc).await.expect_err("the bag gate must fire");
        assert!(
            error.starts_with("unsupported: ")
                && error.contains("list-style indexing/cardinality on a bag"),
            "C1: {source:?} — expected a fail-closed LOWERING error naming the bag, got {error:?}"
        );
    }
}

/// **⚠ THE MEASURED RESIDUE: the bag gate cannot see a carrier that is only known at run time.**
///
/// `[#{1|2|2}#].nth(0)` has receiver type `Bag`, but the outer receiver's *syntax* is a generic
/// `MethodCall`, not `CastBag`, so no shape check at lowering can refuse it — and neither can one
/// refuse a COMM-bound variable.
/// The reducer then measures the bag ABI encoding: **2**. There is no longer a host fold that
/// manufactures an alternate multiset-cardinality answer.
///
/// This is a NEW divergence introduced by C1 (before routing, the whole program failed to lower)
/// and it is recorded here rather than hidden. It is narrow — it needs a bag to reach `length` or
/// `nth` through a value whose carrier the lowering cannot name — and it is NOT closeable by
/// changing `lower_bag`, because the 2-element tagged-`EList` shape is the wire ABI decoded by
/// `run.rs:166`. It closes with **C3**, which gives the machine a real bag algebra instead of an
/// encoding.
///
/// If this test ever starts failing because the machine answers `3`, C3 landed and this witness
/// should be replaced by a conformance row.
#[tokio::test(flavor = "multi_thread")]
async fn c1_bag_length_residue_when_the_carrier_is_only_known_at_runtime() {
    let source = "[#{1 | 2 | 2}#].nth(0).length()";
    let proc = parse(source);
    let observed = reduce(&proc).await.expect("the machine reduces");
    assert_eq!(
        observed.iter().map(render_as_rholang).collect::<Vec<_>>(),
        vec!["2".to_string()],
        "C1 residue: the machine measures the 2-element bag ABI ENCODING. If this is now 3, C3 \
         landed — promote this witness to a conformance row"
    );
}

/// **C1b/C4 — the routed Pathmap/Zipper family now reaches the native trie.**
///
/// These calls are parsed and lowered from Rholang source; there is no synthetic
/// target carrier in this test.  Successful reduction therefore proves that C4
/// removed the former `EMap` carrier block rather than merely adding isolated
/// target-side APIs.
#[tokio::test(flavor = "multi_thread")]
async fn c1b_pathmap_zipper_family_reaches_the_native_carrier() {
    let observed = reduce(&parse("{| 1 : 10, 2 : 20 |}.readZipper().leafCount()"))
        .await
        .expect("readZipper reaches EPathmapBody");
    assert_eq!(
        observed.iter().map(render_as_rholang).collect::<Vec<_>>(),
        vec!["2".to_string()]
    );

    for source in [
        "{| 1 : 10, 2 : 20 |}.readZipper().toNextLeaf().getPath()",
        "{| 1 : 10, 2 : 20 |}.readZipper().childCount()",
        "{| 1 : 10 |}.getSubtrie()",
    ] {
        reduce(&parse(source)).await.unwrap_or_else(|error| {
            panic!("C1b/C4: {source:?} must reach the native trie: {error}")
        });
    }
}

/// **C1/C4 — generic collection methods preserve the native PathMap carrier.**
///
/// Observable lookup/cardinality results pin the relation, while method chains
/// pin carrier preservation: a result accidentally converted to `EMap` would
/// fail when the following zipper method dispatches.
#[tokio::test(flavor = "multi_thread")]
async fn c1_pathmap_methods_answer_through_native_pathmap_storage() {
    assert_reducer_result("{| 1 : 10, 2 : 20 |}.get(1)", "10").await;
    assert_reducer_result("{| 1 : 10, 2 : 20 |}.contains(1)", "true").await;

    for (source, answer) in [
        ("{| 1 : 10, 2 : 20 |}.size()", "2"),
        ("{| 1 : 10, 2 : 20 |}.keys()", "Set(1, 2)"),
        ("{| 1 : 10, 2 : 20 |}.delete(1).size()", "1"),
        ("{| 1 : 10, 2 : 20 |}.set(3, 30).get(3)", "30"),
        ("{| 1 : 10, 2 : 20 |}.union({| 3 : 30 |}).get(3)", "30"),
        ("{| 1 : 10, 2 : 20 |}.set(3, 30).readZipper().leafCount()", "3"),
    ] {
        let observed = reduce(&parse(source)).await.expect("the machine reduces");
        assert_eq!(
            observed.iter().map(render_as_rholang).collect::<Vec<_>>(),
            vec![answer.to_string()],
            "C1/C4: {source:?} must answer through EPathmapBody"
        );
    }
}

/// **`length` on a Map/Set is rejected by the sole method evaluator.**
///
/// Rholang's `length` accepts only list/string/byte-array carriers and spells map/set cardinality
/// `size`. E3 removed the host fold that used to invent a more permissive answer.
#[tokio::test(flavor = "multi_thread")]
async fn c1_length_on_a_map_or_set_is_rejected_by_the_reducer() {
    for (source, other_type) in [("{1 : 10}.length()", "map"), ("Set(1, 2).length()", "set")] {
        let proc = parse(source);
        assert_eq!(
            reduce(&proc).await.expect_err("Rholang spells this `size`"),
            format!(
                r#"reduce: inj: MethodNotDefined {{ method: "length", other_type: "{other_type}" }}"#
            ),
            "C1: {source:?} — Rholang has no `length` for this carrier"
        );
    }
}

/// **The E3 residue: identifiers with NO key in `reduce.rs::method_table` fail closed and named.**
///
/// The grammar accepts each spelling as identifier data and lowering always emits `EMethod`.
/// The reducer's `ReduceError("Unimplemented method: …")` diagnostic is therefore the single,
/// non-duplicated
/// answer. In particular, E3 does not preserve former host-only names (`concat`, `values`, bag
/// `count`/`remove`, or the PathMap aliases) as hidden language semantics.
#[tokio::test(flavor = "multi_thread")]
async fn c1_residue_without_an_interpreter_counterpart_fails_closed_and_named() {
    for (source, method) in [
        ("[1].concat([2])", "concat"),
        (r#""a".concat("b")"#, "concat"),
        ("{1 : 10}.values()", "values"),
        ("#{1 | 2 | 2}#.count(2)", "count"),
        ("#{1 | 2 | 2}#.remove(2)", "remove"),
        ("{| 1 : 10 |}.subtract({| 1 : 10 |})", "subtract"),
        ("{| 1 : 10 |}.restrict({| 1 : 10 |})", "restrict"),
        ("{| 1 : 10 |}.meet({| 1 : 10 |})", "meet"),
        ("{| 1 : 10 |}.getSubtrieAt(1)", "getSubtrieAt"),
    ] {
        let proc = parse(source);
        assert_eq!(
            reduce(&proc).await.expect_err("no counterpart exists"),
            format!(r#"reduce: inj: ReduceError("Unimplemented method: {method}")"#),
            "E3: {source:?} must fail closed through the reducer's method table"
        );
    }
}

/// **★ C1/E3, LANDED — every routed collection method is evaluated by the reducer's own method
/// table.**
///
/// E3 retired the independent method fold bodies. Each row now proves the entire production path:
/// generic `MethodCall` parse, ordered carrier preservation, lowering to `EMethod`, reducer-table
/// dispatch, and observation decoding. There is no second method registry whose agreement can
/// drift or whose extra names can accidentally become language semantics.
///
/// `assert_reducer_result` compares the Rholang-rendered values, so a row passing here also pins the
/// **canonical order** question: a set/map result flowing back from the reducer has been through
/// `ScoredTerm` sorting (`models/src/rust/sorted_par_hash_set.rs`), and `Set(1, 2).union(Set(3))`
/// rendering as `Set(1, 2, 3)` on both sides is the evidence that the two orders coincide for
/// these values — see `c1_routed_results_carry_the_reducer_canonical_order` for the case built to
/// separate them.
#[tokio::test(flavor = "multi_thread")]
async fn c1_target_collection_methods_route_to_the_reducer() {
    // list / string
    assert_reducer_result("[1, 2, 3].length()", "3").await;
    assert_reducer_result("[10, 20, 30].nth(1)", "20").await;
    assert_reducer_result(r#""abc".length()"#, "3").await;
    // set
    assert_reducer_result("Set(1, 2).add(3)", "Set(1, 2, 3)").await;
    assert_reducer_result("Set(1, 2).contains(1)", "true").await;
    assert_reducer_result("Set(1, 2).size()", "2").await;
    assert_reducer_result("Set(1, 2).union(Set(3))", "Set(1, 2, 3)").await;
    assert_reducer_result("Set(1, 2).delete(1)", "Set(2)").await;
    assert_reducer_result("Set(1, 2).diff(Set(1))", "Set(2)").await;
    // map
    assert_reducer_result("{1 : 10}.get(1)", "10").await;
    assert_reducer_result("{1 : 10}.set(2, 20)", "{1:10, 2:20}").await;
    assert_reducer_result("{1 : 10}.contains(1)", "true").await;
    assert_reducer_result("{1 : 10}.size()", "1").await;
    assert_reducer_result("{1 : 10}.keys()", "Set(1)").await;
    assert_reducer_result("{1 : 10}.delete(1)", "{}").await;
    assert_reducer_result("{1 : 10}.union({2 : 20})", "{1:10, 2:20}").await;
    // `.values()` is NOT here: `reduce.rs::method_table` has `keys` but no `values`, so it is
    // MeTTaIL-only residue and belongs to C3 — see
    // `c3_residue_mettail_only_operations_fail_closed_and_named`.
}

/// **The whole point of routing: a COMM-BOUND receiver works exactly like a literal one.**
///
/// This is the capability the demo's value-level filtering needs, and it is the class of bug
/// divergence B is an instance of. It is possible only because `EMethod` dispatches on the
/// *evaluated* receiver — a host-side fold body cannot see through a rendezvous at all.
///
/// The payloads are DELIBERATELY DISTINCTIVE (`424242`, not `3`): the observation is compared as
/// a whole rendered value, but a bare `3` would also appear inside the program text and inside
/// unrelated sends, so a distinctive payload is what makes a green run mean something.
#[tokio::test(flavor = "multi_thread")]
async fn c1_routed_methods_see_through_a_comm() {
    for (program, expected) in [
        (r#"@("c")!([424242, 7, 7]) | for (@x <- @("c")) { @("OUT")!(x.length()) }"#, "3"),
        (
            r#"@("c")!([424242, 7, 7]) | for (@x <- @("c")) { @("OUT")!(x.nth(0)) }"#,
            "424242",
        ),
        (
            r#"@("c")!({424242 : 99}) | for (@x <- @("c")) { @("OUT")!(x.get(424242)) }"#,
            "99",
        ),
        (
            r#"@("c")!(Set(424242)) | for (@x <- @("c")) { @("OUT")!(x.contains(424242)) }"#,
            "true",
        ),
    ] {
        let proc = parse(program);
        let observed = reduce_program(&proc).await.expect("the machine reduces");
        assert_eq!(
            observed.iter().map(render_as_rholang).collect::<Vec<_>>(),
            vec![expected.to_string()],
            "C1: {program:?} — a COMM-bound receiver must dispatch exactly like a literal one"
        );
    }
}

/// **★ Divergence L (NEW, discovered by C1's ordering check 2026-07-26) — Rholang sorts a
/// `Set`/`Map` LEXICOGRAPHICALLY by rendered element; Rholang sorts by `ScoredTerm` VALUE.**
///
/// The two orders coincide on every fixture the suite had before today, which is why this survived
/// unmeasured: they differ only when the rendered forms compare differently from the values, and
/// the smallest such case is **integers of unequal digit count**. `"10" < "2"` as text, `2 < 10`
/// as numbers.
///
/// ⚠ **This is NOT caused by C1, and the first row proves it.** `Set(10, 2)` is a bare literal
/// with no method call anywhere in it — nothing C1 touched can be involved — and it already
/// renders differently on the two sides. The divergence lives in the collection LITERAL: Rholang's
/// own `Set`/`Map` carrier orders its elements one way and `lower_set`/`lower_map` hand the
/// reducer a collection it then sorts its own way (`models/src/rust/sorted_par_hash_set.rs`).
///
/// ## ★ ROOT CAUSE (C4 investigation, 2026-07-26) — and why it must stand for now
///
/// The fold side's order is imposed by the **display codegen**, not by the carrier. A `HashSetLit`
/// is unordered, so the generated `Display` renders each element to a `String` and sorts the
/// STRINGS:
///
/// ```text
///     macros/src/gen/syntax/display.rs
///       :2961  HashSet          parts.push(item.to_string());  … parts.sort();
///       :2968  HashMap/PathMap  parts.push(format!("{k} : {v}")); … parts.sort();
///       :2982  HashBag          …                                  parts.sort();
///     and seven sibling sites (:1717 :1726 :1737 :3224 :3231 :3240 :3317) for the
///     binder-slot and optional-group display paths — ten in total, all `Vec<String>::sort`.
/// ```
///
/// `"10" < "2"` lexicographically; `2 < 10` numerically. Hence `Set(10, 2)`.
///
/// **Why it is not simply fixed here.** The target order is Rholang's `ScoredTerm` order, which is
/// a property of `rhoapi::Par` and of the Rholang sorter — it does not exist for `Proc`. The two
/// available local changes are both wrong in ways that matter more than the symptom:
///
/// 1. *sort the ELEMENTS by `Proc`'s `Ord` instead of their text.* This fixes the witnessed case
///    (integers of unequal digit count) and NOT the general one: `Proc`'s derived `Ord` breaks ties
///    by grammar-declaration order, `ScoredTerm` by term-type score, so mixed-type collections stay
///    divergent. Shipping it would leave the divergence alive only where it is hardest to see —
///    strictly worse than leaving it fully visible, and exactly the silent-wrongness this suite
///    exists to prevent.
/// 2. *change the ten sort sites anyway.* They are LANGUAGE-AGNOSTIC macro codegen shared by every
///    generated language, so this re-renders every collection in the repo to buy a partial fix.
///
/// The honest close is the same one C4 needs and for the same reason: Rholang must stop maintaining
/// a second canonical form for ground data and take the reducer's. Concretely, a per-language
/// canonical-order hook consulted by the display codegen, with Rholang supplying `ScoredTerm`
/// order — which is task 21's "one evaluator" convergence, not a display patch. L and C4 are two
/// symptoms of one root: **Rholang owns a collection carrier whose canonical form is its own.**
///
/// So L stands, deliberately, and this witness keeps it under active measurement.
///
/// What C1 owes here is therefore *consistency, not agreement*: a routed method must return its
/// result in the SAME order the literal already lands in, so routing introduces no NEW ordering
/// behaviour. That is what the second half asserts.
///
/// The reducer is normative, so `Set(2, 10)` is the right answer and Rholang's rendering is the
/// side that is wrong.
///
/// ⚠ A negative literal would be the sharper discriminator — it is where protobuf BYTE order and
/// `ScoredTerm` VALUE order part company, and what made divergence E real for `.toByteArray()`.
/// It is NOT usable here: `Set(3, 1, 2).union(Set(-5))` folds to `Set(-@Nil!(5), 1, 2, 3)`,
/// because a sign-abutted numeric literal is a known LEXER divergence (commit `41f74955`), not a
/// lowering one. Using it would test the lexer, not the ordering.
#[tokio::test(flavor = "multi_thread")]
async fn divergence_l_witness_collection_order_is_lexicographic_in_the_fold() {
    // ① The LITERAL already diverges — no method involved, so this predates C1 entirely.
    for (source, fold_order, machine_order) in [
        ("Set(10, 2)", "Set(10, 2)", "Set(2, 10)"),
        // Insertion order is irrelevant on both sides: both SORT, they just sort differently.
        ("Set(2, 10)", "Set(10, 2)", "Set(2, 10)"),
        ("{10 : 1, 2 : 1}", "{10:1, 2:1}", "{2:1, 10:1}"),
    ] {
        let proc = parse(source);
        assert_eq!(
            fold(&proc).expect("the fold converges"),
            fold_order,
            "L: {source:?} — Rholang orders by the RENDERED element"
        );
        let observed = reduce(&proc).await.expect("the literal lowers");
        assert_eq!(
            observed.iter().map(render_as_rholang).collect::<Vec<_>>(),
            vec![machine_order.to_string()],
            "L: {source:?} — the reducer orders by ScoredTerm VALUE"
        );
    }

    // ② A ROUTED method's result lands in the reducer's order — the SAME order the literal lands
    //    in above. C1 adds no ordering behaviour of its own; it inherits the carrier's.
    for (source, machine_order) in [
        ("Set(10, 2).union(Set(3))", "Set(2, 3, 10)"),
        ("Set(10, 2).add(3)", "Set(2, 3, 10)"),
        ("{10 : 1, 2 : 1}.set(3, 1)", "{2:1, 3:1, 10:1}"),
        ("{10 : 1, 2 : 1}.keys()", "Set(2, 10)"),
    ] {
        let observed = reduce(&parse(source))
            .await
            .expect("the routed method reduces");
        assert_eq!(
            observed.iter().map(render_as_rholang).collect::<Vec<_>>(),
            vec![machine_order.to_string()],
            "L: {source:?} — a routed result carries the reducer's canonical order"
        );
    }

    // ③ Where the literal and routed-result orders COINCIDE, the reducer preserves the values.
    assert_reducer_result("Set(3, 2, 1).add(4)", "Set(1, 2, 3, 4)").await;
    assert_reducer_result(r#"Set("b", "a").add("c")"#, r#"Set("a", "b", "c")"#).await;
    // A List is ordered, not sorted, so a routed list method preserves source order.
    assert_reducer_result("[10, 2, 3].take(3)", "[10, 2, 3]").await;
}

// ════════════════════════════════════════════════════════════════════════════════════════════════
// PART 5 — the adapter's own unit tests
// ════════════════════════════════════════════════════════════════════════════════════════════════

/// [`render_fixed_point`] implements Rholang's `Fixed` surface form; pin it directly so a
/// conformance failure is never mis-attributed to the adapter.
#[test]
fn render_fixed_point_matches_the_rholang_surface_form() {
    assert_eq!(render_fixed_point(&[3], 0), "3p0");
    assert_eq!(render_fixed_point(&[33], 1), "3.3p1");
    assert_eq!(render_fixed_point(&[100], 2), "1.00p2");
    // Fewer digits than the scale ⇒ a leading zero is synthesized.
    assert_eq!(render_fixed_point(&[5], 2), "0.05p2");
    // Negative unscaled values keep the sign outside the digit group.
    assert_eq!(render_fixed_point(&[0xCD], 1), "-5.1p1"); // 0xCD = -51
}

/// The ground-scalar arms of [`render_as_rholang`].
#[test]
fn render_as_rholang_matches_the_rholang_surface_form() {
    assert_eq!(render_as_rholang(&RuntimeObservationValue::Int(-3)), "-3");
    // ★ The `n` tail (divergence I, Stage C): `GBigInt`'s Rholang surface form REQUIRES it —
    // `-7` is the surface form of the `Int` `-7`, a different carrier.
    assert_eq!(render_as_rholang(&RuntimeObservationValue::BigIntBytes(vec![249])), "-7n");
    assert_eq!(render_as_rholang(&RuntimeObservationValue::Bool(false)), "false");
    assert_eq!(
        render_as_rholang(&RuntimeObservationValue::Text("a\"b".to_string())),
        "\"a\\\"b\""
    );
    assert_eq!(
        render_as_rholang(&RuntimeObservationValue::DoubleBits(4.0_f64.to_bits())),
        "4.0"
    );
    assert_eq!(
        render_as_rholang(&RuntimeObservationValue::List(vec![
            RuntimeObservationValue::Int(1),
            RuntimeObservationValue::Int(2),
        ])),
        "[1, 2]"
    );
    assert_eq!(
        render_as_rholang(&RuntimeObservationValue::List(vec![
            RuntimeObservationValue::BigIntBytes(vec![1]),
            RuntimeObservationValue::BigIntBytes(vec![2]),
        ])),
        "[1n, 2n]"
    );
    assert_eq!(
        render_as_rholang(&RuntimeObservationValue::Map(vec![(
            RuntimeObservationValue::Int(1),
            RuntimeObservationValue::Int(10),
        )])),
        "{1:10}"
    );
}

// ════════════════════════════════════════════════════════════════════════════════════════════════
// DIVERGENCE K — the `where`-GUARD LANE (#33 stage D, 2026-07-25)
// ════════════════════════════════════════════════════════════════════════════════════════════════

/// `{ for(@x <- @"c" where GUARD) { @"OUT"!("fired") } | @"c"!(DATUM) }`.
///
/// The COMM fires ⟺ the guard passes, and firing is OBSERVABLE on both legs: the fold's
/// residue loses its `for(`, and the machine rests `"fired"` on `@"OUT"`.
fn guarded_comm_program(guard: &str, datum: &str) -> String {
    format!(r#"{{ for(@x <- @"c" where {guard}) {{ @"OUT"!("fired") }} | @"c"!({datum}) }}"#)
}

/// Did the FOLD fire the COMM? The receive is gone from the residue.
///
/// ⚠ Not `residue.contains("fired")` — the string `"fired"` also appears inside the body of
/// an UNFIRED receive, so that test reports firing for every row. It cost this suite a
/// wrong reading of its own first measurement.
fn fold_fired(residue: &str) -> bool {
    !residue.contains("for(")
}

/// **Divergence K (witness) — the host guard lane BLOCKS a COMM the machine FIRES.**
///
/// ## Why this row did not exist before
///
/// The suite's `fold_program`/`reduce_program` pair found divergences B, D, G, H, I and J,
/// and had **never been pointed at a `where` guard**. The neighbouring
/// `rho_matches_differential.rs` locks the host and machine to the same *verdict*, but its
/// property (1) is one-directional by design — a host `None` is an accepted escape hatch,
/// because "`eval_guard_bool`'s callers treat an undecided guard as *do not fire*
/// host-side". So the VERDICT was locked and the NORMAL FORM was never examined, and the
/// permissive reading of the guard lane survived by never having been tested.
///
/// `formula.rs` states that reading directly: declining "never costs decidability, and it
/// can never produce a wrong answer." That is true of the **verdict** — the host never
/// fires a COMM the machine would not — and false of the **normal form**, which is what
/// this row measures.
///
/// ## Measured 2026-07-25
///
/// ```text
///   guard                                  datum          fold    machine
///   x == true                              true           fires   fires    agree
///   x == true                              false          rests   rests    agree
///   x matches "hi"                         "hi"           fires   fires    agree
///   x matches {true | true}                {true | true}  RESTS   FIRES    ★ diverge
///   (x matches {true | true}) or true      {true | true}  RESTS   FIRES    ★ diverge
///   (x matches {true | true}) or true      false          RESTS   FIRES    ★ diverge
/// ```
///
/// The first three are the controls that prove the instrument works — including
/// `x == true`, which is divergence H's second half and would itself have diverged before
/// stage B1 gave `eval_cmp_order` its `CastBool` arm.
///
/// ★ The last row is the sharpest. Its guard is `(x matches φ) or true`, whose value is
/// forced to `true` by the right operand for EVERY `x`, and whose datum does not even match
/// φ. The machine fires it. The host declines it — because `eval_guard_disposition`'s `Or`
/// arm is LEFT-STRICT, so an undecided left operand short-circuits the whole disjunction to
/// `Declines` before the settling `true` is ever consulted. A guard that is trivially,
/// syntactically true does not fire host-side.
///
/// ## What decides it, and why the obvious fix is not obviously right
///
/// The declining operand is the SEPARATING conjunction `{φ | ψ}`, which
/// `formula::host_matches_verdict` refuses on purpose: its semantics is AC matching with a
/// remainder, and a host re-implementation would be the second, divergent matcher this
/// design exists to avoid. Declining it is correct. Propagating that decline through `or`
/// past a literal `true` is not.
///
/// The fix that suggests itself — make the connectives Kleene, so `unknown ∨ true = true`
/// — is NOT sound in general, and #33 stage B2 is blocked on exactly that: f1r3node
/// evaluates BOTH operands of `EOr`/`EAnd` unconditionally (`reduce.rs` — the work-stack
/// driver pushes `EBool(p2)` and `EBool(p1)` together before `Combine(EvKont::Or)`, and the
/// recursive fallback binds `b1` and `b2` with `?` before combining), and `guard_passes`
/// maps any `Err` or non-boolean result to `false`. So where the undecided operand would
/// ERROR on the machine, a Kleene host fires and the machine does not — unsoundness in the
/// FIRING direction.
///
/// ★ These rows show the two cases are DIFFERENT input classes. Here the undecided operand
/// does not error on the machine; it evaluates fine through the `SpatialMatcherOracle` and
/// returns a boolean. A sound repair therefore has to distinguish "declined because the
/// host may not decide it, though the machine will decide it totally" from "declined
/// because evaluating it may fail" — which is a finer distinction than
/// `GuardDisposition::Declines` currently draws.
///
/// Closed by **#33 stage C** (making the residue honest), which is why this is a witness
/// and not a bug report.
#[tokio::test(flavor = "multi_thread")]
async fn divergence_k_witness_guard_lane_blocks_a_comm_the_machine_fires() {
    // ── controls: the instrument fires and rests where it should ──
    for (guard, datum, expected) in [
        ("x == true", "true", true),
        ("x == true", "false", false),
        (r#"x matches "hi""#, r#""hi""#, true),
    ] {
        let proc = parse(&guarded_comm_program(guard, datum));
        let residue = fold_program(&proc).expect("the COMM+fold fixpoint settles");
        let observed = reduce_program(&proc).await.expect("the machine reduces");
        assert_eq!(
            fold_fired(&residue),
            expected,
            "control {guard:?} on {datum:?}: fold should {} — got {residue:?}",
            if expected { "fire" } else { "rest" }
        );
        assert_eq!(
            !observed.is_empty(),
            expected,
            "control {guard:?} on {datum:?}: machine should {}",
            if expected { "fire" } else { "rest" }
        );
    }

    // ── ★ the divergence: host rests, machine fires ──
    for (guard, datum) in [
        (r#"x matches {true | true}"#, "{true | true}"),
        (r#"(x matches {true | true}) or true"#, "{true | true}"),
        (r#"(x matches {true | true}) or true"#, "false"),
    ] {
        let proc = parse(&guarded_comm_program(guard, datum));
        let residue = fold_program(&proc).expect("the COMM+fold fixpoint settles");
        let observed = reduce_program(&proc).await.expect("the machine reduces");
        assert!(
            !fold_fired(&residue),
            "K: the host is expected to DECLINE {guard:?} on {datum:?} today and leave the \
             receive resting; if it now fires, stage C landed and this witness must be \
             replaced by its target twin. Got {residue:?}"
        );
        assert_eq!(
            observed.iter().map(render_as_rholang).collect::<Vec<_>>(),
            vec![r#""fired""#.to_string()],
            "K: the MACHINE fires {guard:?} on {datum:?} — that is the whole point of the \
             divergence, and if it stops firing the reducer's guard semantics changed"
        );
    }
}

/// **Divergence K (target) — the guard lane's normal form agrees with the machine.**
///
/// The reducer is NORMATIVE ("rholang IS rholang"), so where the two disagree the host is
/// wrong. This asserts the property the witness above measures the absence of: for a guard
/// the machine decides, the fold's residue reflects the same decision.
///
/// It is stated as AGREEMENT rather than as "the host must fire", because the repair is not
/// required to make the host decide these guards itself — leaving the COMM to the machine
/// is legitimate. What is not legitimate is a *residue that looks settled* while the
/// machine would have reduced it further. Stage C makes the residue say which of the two
/// occurred, at which point this test becomes satisfiable without the host re-implementing
/// the spatial matcher.
///
/// Closed by **#33 stage C**.
#[tokio::test(flavor = "multi_thread")]
#[ignore = "divergence K: the host guard lane conflates `cannot decide` with `decided false`, \
            so it rests where the machine fires (e.g. `(x matches {φ|ψ}) or true`, a guard \
            forced true by its right operand); closed by #33 stage C"]
async fn divergence_k_target_guard_lane_normal_form_agrees_with_the_machine() {
    for (guard, datum) in [
        (r#"x matches {true | true}"#, "{true | true}"),
        (r#"(x matches {true | true}) or true"#, "{true | true}"),
        (r#"(x matches {true | true}) or true"#, "false"),
    ] {
        let proc = parse(&guarded_comm_program(guard, datum));
        let residue = fold_program(&proc).expect("the COMM+fold fixpoint settles");
        let observed = reduce_program(&proc).await.expect("the machine reduces");
        assert_eq!(
            fold_fired(&residue),
            !observed.is_empty(),
            "K: fold and machine must agree on whether {guard:?} fires on {datum:?}; \
             fold residue {residue:?} vs machine {:?}",
            observed.iter().map(render_as_rholang).collect::<Vec<_>>()
        );
    }
}

// ════════════════════════════════════════════════════════════════════════════════════════════════
// DIVERGENCE K, THE BOUNDARY — the defect is in the GUARD lane, NOT in the FORMULA lane
// (#33 stage D, 2026-07-25)
// ════════════════════════════════════════════════════════════════════════════════════════════════

/// **`formula::kleene_or` is sound, and the hazard divergence K exhibits does not reach it.**
///
/// ## The question this closes
///
/// Divergence K's sharpest row is `(x matches {φ|ψ}) or true` — a guard forced `true` by its
/// right operand that the host nevertheless declines. Rholang spells `or` at TWO levels, and
/// only one of them is the one that misbehaves:
///
/// ```text
///   GUARD level     (x matches φ) or (x matches ψ)   Proc::Or        ⟶  EOr        ⟶  evaluated
///   FORMULA level   x matches (φ or ψ)               FormulaShape::  ⟶  ConnOrBody ⟶  MATCHED
///                                                    Disjunction
/// ```
///
/// The guard-level `or` is `eval_guard_disposition`'s `Or` arm (left-strict: `Declines =>
/// Declines`). The formula-level `or` is `formula::kleene_or`, which is FULL Kleene —
/// `kleene_or(unknown, true) = true`, exactly the rule the guard lane refuses. Since the guard
/// lane refuses it on soundness grounds, the obvious worry is that the formula lane, which
/// already applies it, is unsound today.
///
/// **It is not, and this test measures that rather than arguing it.**
///
/// ## ① Which rows even reach `kleene_or` (measured 2026-07-25)
///
/// `host_matches_verdict` runs an `is_statically_true`/`is_statically_false` PRE-PASS before it
/// classifies, and `is_statically_true(φ ∨ ψ)` is `is_statically_true(φ) || is_statically_true(ψ)`.
/// So the disjunction that looks like the natural probe is answered before the Kleene table is
/// ever consulted:
///
/// ```text
///   formula                        static_true  static_false  reaches kleene_or?
///   {true | true} or true          TRUE         false         NO — pre-pass answers Some(true)
///   "hi" or "bye"                  false        false         yes
///   "hi" or {true | @"a"!(1)}      false        false         yes
///   {true | @"a"!(1)} or "hi"      false        false         yes
///   (not "hi") or (not "hi")       false        false         yes
/// ```
///
/// ## ② The operand verdicts `kleene_or` is actually fed, on the target `"hi"`
///
/// ```text
///   host_matches_verdict("hi", "hi")                 Some(true)    a PROVED match
///   host_matches_verdict("hi", "bye")                None          declined (positive-only term arm)
///   host_matches_verdict("hi", {true | @"a"!(1)})    None          declined (SEPARATING conjunction)
///   host_matches_verdict("hi", not "hi")             Some(false)   a PROVED non-match
/// ```
///
/// so the four live rows exercise `kleene_or(T,?)`, `kleene_or(T,?)`, **`kleene_or(?,T)`** and
/// `kleene_or(F,F)` — including the exact cell the guard lane refuses.
///
/// ## ③ Every formula-level row AGREES with the machine
///
/// ```text
///   guard                                  datum   fold    machine
///   x matches ({true | true} or true)      false   fires   fires    agree
///   x matches ({true | true} or true)      {t | t} fires   fires    agree
///   x matches ("hi" or "bye")              "hi"    fires   fires    agree
///   x matches ("hi" or {true | @"a"!(1)})  "hi"    fires   fires    agree
///   x matches ({true | @"a"!(1)} or "hi")  "hi"    fires   fires    agree   ★ kleene_or(?,T)
///   x matches ((not "hi") or (not "hi"))   "hi"    rests   rests    agree
/// ```
///
/// ## ④ ★ The contrast that localizes the defect
///
/// The last formula row and this guard row have the SAME two operands and the SAME datum. Only
/// the position of `or` differs — and the host's answer flips while the machine's does not:
///
/// ```text
///   x matches ({true | @"a"!(1)} or "hi")               "hi"   fires   fires   agree
///   (x matches {true | @"a"!(1)}) or (x matches "hi")   "hi"   RESTS   FIRES   ★ diverge (K)
/// ```
///
/// ## Why the strictness argument does not transfer
///
/// A formula is never EVALUATED. `t matches φ` lowers to one `EMatches{target, pattern}`
/// (`rholang_ast.rs`'s `Matches` arm): the target is evaluated, the pattern is handed verbatim to
/// the reducer's spatial matcher, and `ConnOrBody` there is a `find_map` over the disjuncts
/// (f1r3node `rholang/src/rust/interpreter/matcher/spatial_matcher.rs`) — a disjunct that does not
/// match simply yields `None` from the closure and the search moves on. **There is no error
/// channel**, so the failure mode that blocks stage B2 — f1r3node evaluating BOTH operands of
/// `EOr` and `guard_passes` mapping any `Err` or non-boolean to `false` — has nothing to act on.
///
/// Composed with `host_matches_verdict`'s positive-only containment lemma (a host match PROVES a
/// machine match) and `ConnOr = ∃`, `kleene_or(Some(true), _) = Some(true)` is exactly as sound as
/// the term arm it rests on; `kleene_or(Some(false), Some(false))` is sound because in this
/// lattice a `Some(false)` is only ever produced by a proof of non-match, never by a failure to
/// find one.
///
/// ★ The consequence for **#33 stage C / B2**: the repair belongs in
/// `receive::eval_guard_disposition`, NOT in `formula.rs`. Changing `kleene_or` would be fixing
/// the lane that is already correct.
#[tokio::test(flavor = "multi_thread")]
async fn formula_level_disjunction_agrees_where_the_guard_level_or_diverges() {
    use mettail_languages::rholang::formula::{
        host_matches_verdict, is_statically_false, is_statically_true,
    };

    // ── ① the static pre-pass decides WHICH rows reach the Kleene table ──
    let named_probe = parse("{true | true} or true");
    assert!(
        is_statically_true(&named_probe),
        "`{{true | true}} or true` is answered by the is_statically_true PRE-PASS, so it never \
         reaches kleene_or; the disjunction-with-a-`true`-disjunct probe cannot test the Kleene \
         table at all"
    );
    for formula_src in [
        r#""hi" or "bye""#,
        r#""hi" or {true | @"a"!(1)}"#,
        r#"{true | @"a"!(1)} or "hi""#,
        r#"(not "hi") or (not "hi")"#,
    ] {
        let formula = parse(formula_src);
        assert!(
            !is_statically_true(&formula) && !is_statically_false(&formula),
            "{formula_src:?} must be statically UNDECIDED, or it would be short-circuited by the \
             pre-pass and these rows would not exercise kleene_or at all"
        );
    }

    // ── ② the operand verdicts kleene_or is fed, on the target `"hi"` ──
    let target = parse(r#""hi""#);
    for (operand_src, expected) in [
        (r#""hi""#, Some(true)),
        (r#""bye""#, None),
        (r#"{true | @"a"!(1)}"#, None),
        (r#"(not "hi")"#, Some(false)),
    ] {
        assert_eq!(
            host_matches_verdict(&target, &parse(operand_src)),
            expected,
            "the operand {operand_src:?} on the target \"hi\" pins which kleene_or CELL the rows \
             below exercise; if this moves, they stop testing what this test says they test"
        );
    }

    // ── ③ every FORMULA-level disjunction agrees with the machine ──
    for (guard, datum, fires) in [
        (r#"x matches ({true | true} or true)"#, "false", true),
        (r#"x matches ({true | true} or true)"#, "{true | true}", true),
        (r#"x matches ("hi" or "bye")"#, r#""hi""#, true),
        (r#"x matches ("hi" or {true | @"a"!(1)})"#, r#""hi""#, true),
        // ★ kleene_or(unknown, true) — the cell the guard lane refuses as unsound.
        (r#"x matches ({true | @"a"!(1)} or "hi")"#, r#""hi""#, true),
        (r#"x matches ((not "hi") or (not "hi"))"#, r#""hi""#, false),
    ] {
        let proc = parse(&guarded_comm_program(guard, datum));
        let residue = fold_program(&proc).expect("the COMM+fold fixpoint settles");
        let observed = reduce_program(&proc).await.expect("the machine reduces");
        assert_eq!(
            fold_fired(&residue),
            fires,
            "the FOLD must {} {guard:?} on {datum:?} — got {residue:?}",
            if fires { "fire" } else { "rest" }
        );
        assert_eq!(
            !observed.is_empty(),
            fires,
            "the MACHINE must {} {guard:?} on {datum:?} — got {:?}",
            if fires { "fire" } else { "rest" },
            observed.iter().map(render_as_rholang).collect::<Vec<_>>()
        );
    }

    // ── ④ ★ the guard-level twin of the fifth row above: same operands, same datum, DIVERGES ──
    let twin = r#"(x matches {true | @"a"!(1)}) or (x matches "hi")"#;
    let proc = parse(&guarded_comm_program(twin, r#""hi""#));
    let residue = fold_program(&proc).expect("the COMM+fold fixpoint settles");
    let observed = reduce_program(&proc).await.expect("the machine reduces");
    assert!(
        !fold_fired(&residue),
        "divergence K: moving the SAME disjunction from formula position to guard position must \
         still make the host decline today, because eval_guard_disposition's Or arm is \
         left-strict; if it now fires, stage C landed and the K witness must be replaced by its \
         target twin. Got {residue:?}"
    );
    assert_eq!(
        observed.iter().map(render_as_rholang).collect::<Vec<_>>(),
        vec![r#""fired""#.to_string()],
        "divergence K: the MACHINE fires the guard-level twin, which is what makes the host's \
         decline a divergence rather than a shared abstention"
    );
}

// ════════════════════════════════════════════════════════════════════════════════════════════════
// PART 6 — ★ the zipper-exhaustion CROSS-ENDPOINT CONTRACT
//
// The two runtimes report an exhausted `toNextLeaf()` walk DIFFERENTLY, on purpose:
//
//   | runtime                          | exhausted `toNextLeaf`          |
//   |----------------------------------|---------------------------------|
//   | the Rholang interpreter (f1r3node) | `Ok(Par::default())` = **Nil**  |
//   | mettail / Rholang                | `Err(())` = **stuck**           |
//
// Mistranslating this does not raise an error — it LOOPS FOREVER. `pathmap`'s `to_next_val()`
// RESETS the zipper to the root when the walk finishes (`pathmap/src/zipper.rs:546`), so the
// position handed back on exhaustion is a perfectly valid ROOT zipper. Anything that surfaced it
// as a usable `ReadZipper` would silently restart the counted walk from the first leaf and never
// terminate, with nothing anywhere reporting a fault.
//
// The contract is pinned on both sides by tests that name each other:
//   * f1r3node: `rholang/tests/zipper_enumeration_spec.rs::to_next_leaf_returns_nil_when_exhausted`
//   * mettail:  `languages/src/rholang/zipper.rs::exhausted_walk_is_stuck_here_and_nil_on_the_reducer`
//     (and the surface-level `languages/tests/rholang_tests.rs::zipper_leaf_walk_exhaustion_stays_stuck`)
//
// This section is C1's half: it proves the property END-TO-END against the REAL reducer, over the
// exact `EMethod` chain the C1b lowering emits, and BOUNDED so a violation FAILS instead of
// hanging the suite.
// ════════════════════════════════════════════════════════════════════════════════════════════════

use models::rhoapi::expr::ExprInstance as ZExprInstance;
use models::rhoapi::Expr as ZExpr;
use models::rhoapi::{EEq as ZEEq, EList as ZEList, EMethod as ZEMethod, EPathMap as ZEPathMap};

fn zipper_expr_par(instance: ZExprInstance) -> Par {
    Par::default().with_exprs(vec![ZExpr { expr_instance: Some(instance) }])
}

/// A set-specialized `EPathMap` over the given elements.  Each member is its
/// canonical trie key and the semantic value returned by `getLeaf`.
fn zipper_epathmap(elements: Vec<Par>) -> Par {
    zipper_expr_par(ZExprInstance::EPathmapBody(ZEPathMap::new(elements, Vec::new(), false, None)))
}

/// A map-specialized `EPathMap`; keys remain canonical compressed paths while
/// the associated `Par`s occupy PathMap value slots.
fn zipper_epathmap_map(entries: Vec<(Par, Par)>) -> Par {
    zipper_expr_par(ZExprInstance::EPathmapBody(ZEPathMap::new_map(
        entries,
        Vec::new(),
        false,
        None,
    )))
}

fn zipper_gstring(text: &str) -> Par {
    zipper_expr_par(ZExprInstance::GString(text.to_string()))
}

fn zipper_elist(items: Vec<Par>) -> Par {
    zipper_expr_par(ZExprInstance::EListBody(ZEList {
        ps: items,
        locally_free: Vec::new(),
        connective_used: false,
        remainder: None,
    }))
}

/// `target.name(arguments)` as the reducer sees it — byte-identical in shape to what
/// `rholang_ast.rs::lower_method` emits for the routed zipper family.
fn zipper_method(name: &str, target: Par, arguments: Vec<Par>) -> Par {
    zipper_expr_par(ZExprInstance::EMethodBody(ZEMethod {
        method_name: name.to_string(),
        target: Some(target),
        arguments,
        locally_free: Vec::new(),
        connective_used: false,
    }))
}

/// Evaluate a hand-built EXPRESSION on the real reducer by grafting it into the payload slot of a
/// lowered `@("OUT")!(Nil)`, so the send/observe scaffolding is mettail's production one and only
/// the expression under test is synthetic.
async fn reduce_expression(expression: Par) -> Result<Vec<RuntimeObservationValue>, String> {
    clear_held_fold_sites();
    let scaffold = parse(r#"@("OUT")!(Nil)"#);
    let mut par = lower_rholang_proc(&scaffold).expect("the @(\"OUT\")!(Nil) scaffold lowers");
    assert_eq!(par.sends.len(), 1, "the scaffold must lower to exactly one send");
    par.sends[0].data = vec![expression];
    let definitions =
        fold_definitions_for(&take_held_fold_sites()).expect("the scaffold records no fold sites");
    run_installed_program_with_call_definitions_and_read_runtime_values(
        &Par::default(),
        &par,
        definitions,
        "OUT",
    )
    .await
    .map_err(|err| format!("reduce: {err}"))
}

/// Four entries. Byte-lex order over the first segment is `"a" < "b" < "c"`, so the depth-first
/// LEAF order is `["a","x"]`, `["a","y"]`, `["b"]`, `["c","z"]` — the same fixture, and the same
/// documented order, as the f1r3node twin spec's `MAP`.
fn four_leaf_pathmap() -> Par {
    zipper_epathmap(vec![
        zipper_elist(vec![zipper_gstring("a"), zipper_gstring("x")]),
        zipper_elist(vec![zipper_gstring("a"), zipper_gstring("y")]),
        zipper_elist(vec![zipper_gstring("b")]),
        zipper_elist(vec![zipper_gstring("c"), zipper_gstring("z")]),
    ])
}

/// Three entries whose elements are **BARE** (not ground lists): `1`, `2`, `3`.
///
/// `pathmap_integration::par_to_path` splits only a ground `EList` into per-element segments; every
/// other Par yields ONE segment. So this fixture is the second of the carrier's two element shapes,
/// and it is the shape whose whole enumeration surface C4 measured as defective and
/// [`c4_a_bare_element_reads_back_as_itself`] now measures as sound.
fn bare_element_pathmap() -> Par {
    zipper_epathmap(vec![
        zipper_expr_par(ZExprInstance::GInt(1)),
        zipper_expr_par(ZExprInstance::GInt(2)),
        zipper_expr_par(ZExprInstance::GInt(3)),
    ])
}

/// `root` followed by `steps` × `.toNextLeaf()`, for any zipper-valued `root`.
///
/// Generalised by C4 so the exhaustion contract can be exercised from a NON-root focus and over
/// element shapes other than the ground-list one — see
/// [`c1_zipper_walk_exhaustion_terminates_within_leaf_count`].
fn walk_from(root: Par, steps: usize) -> Par {
    let mut zipper = root;
    for _ in 0..steps {
        zipper = zipper_method("toNextLeaf", zipper, Vec::new());
    }
    zipper
}

/// `m.readZipper()` followed by `steps` × `.toNextLeaf()`.
fn leaf_walk(steps: usize) -> Par {
    walk_from(zipper_method("readZipper", four_leaf_pathmap(), Vec::new()), steps)
}

/// `walk == Nil` — the reducer's own exhaustion test, as a `GBool`.
fn walk_is_nil(steps: usize) -> Par {
    walk_from_is_nil(zipper_method("readZipper", four_leaf_pathmap(), Vec::new()), steps)
}

/// `value == Nil`, as a `GBool`.
///
/// `Nil` is `Par::default()`, which renders as the EMPTY observation, so "did this answer `Nil`?"
/// cannot be read off the rendering — comparing against `Nil` in the reducer is the reliable probe.
fn reads_as_nil(value: Par) -> Par {
    zipper_expr_par(ZExprInstance::EEqBody(ZEEq {
        p1: Some(value),
        p2: Some(Par::default()),
    }))
}

/// `walk_from(root, steps) == Nil` — the reducer's own exhaustion test, as a `GBool`.
fn walk_from_is_nil(root: Par, steps: usize) -> Par {
    reads_as_nil(walk_from(root, steps))
}

/// **★ THE EXHAUSTION TEETH-TEST — the walk terminates within `leafCount()` + 1 steps.**
///
/// This is the test that would loop forever if the translation were wrong, made BOUNDED so that it
/// fails instead. It searches for the first step at which the walk becomes `Nil`, scanning only as
/// far as `leafCount() + 1`. If exhaustion were surfaced as a usable zipper, `to_next_val`'s
/// reset-to-root would make the walk restart, no step in range would ever be `Nil`, the search
/// would run off the end, and the assertion below FAILS — loudly, in bounded time.
///
/// The `Nil` must land at exactly `leafCount() + 1`: `leafCount()` steps to visit the four leaves,
/// and one more to fall off the end.
#[tokio::test(flavor = "multi_thread")]
async fn c1_zipper_walk_exhaustion_terminates_within_leaf_count() {
    // ★ C4 EXTENSION (2026-07-26) — ADVANCEMENT, and the two rows that measured a defect.
    //
    // The original test asked one question: does the walk become `Nil` at `leafCount() + 1`? That
    // is necessary but not sufficient. A walk can exhaust exactly on schedule while REVISITING one
    // leaf and skipping another, and the counted idiom would then read the right NUMBER of entries
    // and the wrong entries. So this version also requires the walk to ADVANCE — every step's
    // `getPath()` differs from the step before — which is exactly the property the bare-element
    // carrier used to violate.
    //
    // ⚠ TWO further rows were written first and both FAILED. Neither was weakened away; each was
    // promoted to its own test, because each failure was the measurement:
    //
    //   * a SUBTRIE root (`readZipperAt(["a"])`, branch count 2) never became `Nil` at 3 — the walk
    //     is MAP-scoped and leaves the branch at step 3. That one is a genuine property of the
    //     contract's SCOPE and stays promoted, at
    //     [`c4_a_subtrie_walk_is_bounded_by_the_count_not_by_nil`].
    //   * BARE (non-list) elements never became `Nil` at all — the walk was a FIXED POINT at the
    //     first leaf, so a walk-until-`Nil` over `{| 1, 2, 3 |}` did not terminate.
    //
    // ★★ THE BARE ROW IS RESTORED (2026-07-27). That second failure was an INTERPRETER defect, not
    // a property of this contract, and the interpreter is fixed — so the row comes back to where it
    // was written rather than living on as a witness. Measured over `{| 1, 2, 3 |}`:
    //
    //     step        1     2     3     4          leafCount() == 3
    //     getPath()   1     2     3     ✗ error    ← ADVANCES, and the paths are BARE
    //     == Nil ?    F     F     F     true       ← exhausts at leafCount() + 1
    //
    // Three f1r3node commits closed it, and NEITHER of the two fixes the retired witnesses proposed
    // is among them; the full derivation is on [`c4_a_bare_element_reads_back_as_itself`]. What
    // matters here is that the exhaustion contract is now carrier-INDEPENDENT: it holds for the
    // ground-list element shape and for the bare one, under one identical body.
    for (label, root, expected_leaf_count) in [
        (
            "whole map, GROUND-LIST elements",
            zipper_method("readZipper", four_leaf_pathmap(), Vec::new()),
            4usize,
        ),
        (
            "whole map, BARE elements",
            zipper_method("readZipper", bare_element_pathmap(), Vec::new()),
            3usize,
        ),
    ] {
        // The DECIDABLE BOUND. A stuck term is not an end-test, which is precisely why
        // `leafCount()` exists and why it — not a "did it fail?" probe — terminates a counted walk.
        let counted = reduce_expression(zipper_method("leafCount", root.clone(), Vec::new()))
            .await
            .unwrap_or_else(|err| panic!("{label}: leafCount() at the root must reduce: {err}"));
        assert_eq!(
            counted.iter().map(render_as_rholang).collect::<Vec<_>>(),
            vec![expected_leaf_count.to_string()],
            "{label}: leafCount() is the walk bound at THIS root — the map's cardinality at the \
             root, and the BRANCH's count at a prefix"
        );
        let leaf_count = expected_leaf_count;

        // Bounded search for the first exhausted step. `+ 1` is the whole budget: one step per
        // leaf, plus the step that falls off the end.
        let mut first_nil_at = None;
        for steps in 1..=(leaf_count + 1) {
            let observed = reduce_expression(walk_from_is_nil(root.clone(), steps))
                .await
                .unwrap_or_else(|err| {
                    panic!("{label}: `walk == Nil` must reduce to a Bool at step {steps}: {err}")
                });
            let rendered = observed.iter().map(render_as_rholang).collect::<Vec<_>>();
            assert_eq!(
                rendered.len(),
                1,
                "{label} step {steps}: expected exactly one Bool observation"
            );
            match rendered[0].as_str() {
                "true" => {
                    first_nil_at = Some(steps);
                    break;
                },
                "false" => continue,
                other => {
                    panic!("{label} step {steps}: `walk == Nil` must be a Bool, got {other:?}")
                },
            }
        }

        assert_eq!(
            first_nil_at,
            Some(leaf_count + 1),
            "★ EXHAUSTION CONTRACT VIOLATED ({label}). The walk must become Nil at exactly \
             leafCount()+1 = {}. `None` here means it never exhausted within the bound — i.e. the \
             walk RESTARTED, which is the infinite loop this test exists to catch (`to_next_val` \
             resets to the root on exhaustion). A smaller value means the walk ended early and \
             entries were skipped.",
            leaf_count + 1
        );

        // ★ ADVANCEMENT. Exhausting on schedule is not enough — the walk must MOVE at every step.
        // A fixed point or a cycle would satisfy the bound above while reading one entry `n` times.
        let mut previous: Option<String> = None;
        for steps in 1..=leaf_count {
            let observed =
                reduce_expression(zipper_method("getPath", walk_from(root.clone(), steps), vec![]))
                    .await
                    .unwrap_or_else(|err| {
                        panic!("{label} step {steps}: getPath() must reduce: {err}")
                    });
            let rendered = observed.iter().map(render_as_rholang).collect::<Vec<_>>();
            assert_eq!(rendered.len(), 1, "{label} step {steps}: expected one observation");
            if let Some(previous) = previous {
                assert_ne!(
                    previous, rendered[0],
                    "★ ADVANCEMENT VIOLATED ({label}). Step {steps} is parked on the SAME entry as \
                     step {}. The walk exhausts on schedule and still enumerates the wrong set — \
                     this is the failure mode a Nil-only test cannot see.",
                    steps - 1
                );
            }
            previous = Some(rendered[0].clone());
        }
    }
}

/// **The walk visits every entry exactly once, in depth-first order, and BOTH accessors answer.**
///
/// The counterpart to the bound: it is not enough that the walk stops: it must stop having seen
/// everything, exactly once, in the documented order. `getPath()` answering at every stop is what
/// makes a separate "is there a value here?" predicate unnecessary.
#[tokio::test(flavor = "multi_thread")]
async fn c1_zipper_counted_walk_visits_every_leaf_once_in_order() {
    for (steps, expected_path) in [
        (1usize, r#"["a", "x"]"#),
        (2, r#"["a", "y"]"#),
        (3, r#"["b"]"#),
        (4, r#"["c", "z"]"#),
    ] {
        let observed = reduce_expression(zipper_method("getPath", leaf_walk(steps), Vec::new()))
            .await
            .unwrap_or_else(|err| panic!("getPath() after {steps} steps must reduce: {err}"));
        assert_eq!(
            observed.iter().map(render_as_rholang).collect::<Vec<_>>(),
            vec![expected_path.to_string()],
            "step {steps}: the depth-first leaf order is a documented part of the contract"
        );
    }
}

/// **★ A walk CANNOT continue on the exhausted `Nil` — the second half of the translation.**
///
/// "Never surface `Nil` as a usable `ReadZipper`; never let a walk continue on it." On this side
/// the guarantee is structural rather than defensive, and that is stronger than a check: `Nil` is
/// `Par::default()`, which carries no `EZipperBody`, so the reducer's own zipper methods cannot
/// accept it. Stepping past exhaustion is a hard error, NOT a silent restart from the first leaf.
///
/// Both probes below are one step beyond where [`c1_zipper_walk_exhaustion_terminates_within_leaf_count`]
/// found the `Nil`.
///
/// ── ★ THE TWO EXHAUSTION SURFACES ARE DIFFERENT QUESTIONS (settled 2026-07-27) ───────────────────
///
/// A reader who knows only that the contract says `walk == Nil` can reasonably expect `getPath()`
/// at that step to answer `Nil` too. It does not — it RAISES. Both are correct, because they ask
/// different questions of the sentinel:
///
/// | expression                     | at `leafCount() + 1`                    | why                |
/// |-------------------------------|-----------------------------------------|--------------------|
/// | `walk == Nil`                  | `true`                                  | the SENTINEL TEST  |
/// | `walk.getPath()`               | `ReduceError`                            | an ACCESSOR ON it  |
/// | `walk.toNextLeaf()` (step + 1) | `ReduceError`                            | a MOVE from it     |
///
/// The sentinel is comparison, which every Par supports. An accessor is a METHOD, and `Nil` is
/// `Par::default()` — zero `exprs`, no `EZipperBody` — so `eval_single_expr`'s dispatch has no
/// receiver to match and fails closed BEFORE any zipper code runs. That is the whole guarantee this
/// test exists for: exhaustion is unusable rather than silently root-reset.
///
/// ⚠ The MESSAGE is misleading and is deliberately so upstream. `Nil` has ZERO expressions, and the
/// text says *"Multiple expressions given."* — it is `eval_single_expr`'s `_`-arm
/// (`reduce.rs::descend_single`, `match p.exprs.as_slice() { [e] => …, _ => Err(…) }`), which
/// catches both zero and many. f1r3node names this exact string `NIL_MID_CHAIN_ERROR`
/// (`fused_pathmap_chain.rs`, *"the misleading string IS the pin"*) and asserts it as the PM-4(d)
/// Nil-source parity target in `rholang/tests/epathmap_differential_scaffold.rs`, so the fused
/// chain and the unfused one fail identically. It is a diagnostic-quality wart with a consensus
/// obligation attached, NOT a semantic defect — pinned here rather than worked around, and
/// asserted as EQUAL ACROSS CARRIERS so a bare-element chain cannot start failing differently.
#[tokio::test(flavor = "multi_thread")]
async fn c1_zipper_walk_cannot_continue_past_exhaustion() {
    let leaf_count = 4usize;

    // ① The SENTINEL answers cleanly at `leafCount() + 1`. This is the contract every walk body
    //    tests, and it is the reason the raises below are not a contradiction.
    let sentinel = reduce_expression(walk_is_nil(leaf_count + 1))
        .await
        .expect("the exhaustion sentinel must reduce to a Bool");
    assert_eq!(
        sentinel.iter().map(render_as_rholang).collect::<Vec<_>>(),
        vec!["true".to_string()],
        "★ `walk == Nil` IS the exhaustion test, and it must answer — a walk body that follows the \
         documented contract never reaches the accessor raises below"
    );

    // `toNextLeaf()` ON the exhausted Nil.
    let stepped = reduce_expression(leaf_walk(leaf_count + 2)).await;
    assert!(
        stepped.is_err(),
        "★ stepping past exhaustion must FAIL. Getting a value here means the walk restarted from \
         the root — the infinite loop. Got {stepped:?}"
    );

    // `getPath()` ON the exhausted Nil — the accessor a walk body would call.
    let path =
        reduce_expression(zipper_method("getPath", leaf_walk(leaf_count + 1), Vec::new())).await;
    assert!(
        path.is_err(),
        "★ reading a path out of the exhausted Nil must FAIL, not answer the first leaf. Got {path:?}"
    );

    // ② The exact fail-closed shape, and the fact that it does not depend on the element shape.
    //    A carrier-DEPENDENT failure mode here would be a real defect: the two element shapes would
    //    need two different walk bodies.
    let bare_root = zipper_method("readZipper", bare_element_pathmap(), Vec::new());
    let bare_path =
        reduce_expression(zipper_method("getPath", walk_from(bare_root, 3 + 1), Vec::new()))
            .await
            .expect_err(
                "★ the bare carrier must fail closed at exhaustion, exactly as the list one",
            );
    let list_path = path.expect_err("checked immediately above");
    assert_eq!(
        bare_path, list_path,
        "★ the exhausted-accessor failure must be the SAME for BARE and GROUND-LIST elements — a \
         difference here means the two shapes need two walk bodies"
    );
    assert_eq!(
        list_path, r#"reduce: inj: ReduceError("Error: Multiple expressions given.")"#,
        "★ PM-4(d): the exhausted accessor raises `eval_single_expr`'s `_`-arm. `Nil` has ZERO \
         expressions, so the wording is wrong and DELIBERATELY pinned upstream \
         (`fused_pathmap_chain.rs::NIL_MID_CHAIN_ERROR`) because the fused chain must fail with \
         the identical string. If this moves, mettail is reading a DIFFERENT failure than the one \
         f1r3node's own differential asserts"
    );
}

/// **The Rholang side of the same fixture still reports exhaustion as STUCK — the two conventions,
/// measured side by side.**
///
/// The fold path is unchanged by C1, and this pins that the mismatch documented in
/// `languages/src/rholang/zipper.rs` is still exactly what it says it is: where the reducer
/// answers `Nil`, Rholang's `.toNextLeaf()` leaves the term unreduced. A stuck term still DISPLAYS
/// the method call, which is how "stuck" is observed here.
#[tokio::test(flavor = "multi_thread")]
async fn c1_rholang_side_still_reports_exhaustion_as_stuck() {
    // Two entries, so the third step is one past the end.
    let source = "{| 1 : 10, 2 : 20 |}.readZipper().toNextLeaf().toNextLeaf().toNextLeaf()";
    let residue = fold(&parse(source)).expect("the fold converges");
    assert!(
        residue.contains("toNextLeaf"),
        "the exhausted Rholang walk must stay STUCK (the call survives in the normal form), which \
         is the convention the reducer's Nil has to be translated FROM. Got {residue:?}"
    );
}

/// **★ Every routed zipper/pathmap method is exercised against a REAL `EPathMap` — the check that
/// caught the historical `setLeaf` mismatch.**
///
/// A shared method NAME is not a shared operation, and this family is the one place where that
/// cannot be checked completely by ordinary observation rows because zipper
/// and pathmap results have no `RuntimeObservationValue` variant. Without this
/// test the family would be routed on the strength of name matching alone.
///
/// It already earned its keep. `setLeaf` is **not** in the list below because this check found that
/// Rholang's `w.setLeaf(full, v)` writes at an ABSOLUTE PATH ARGUMENT while Rholang's
/// `z.setLeaf(v)` writes at the zipper's FOCUS and takes one argument — the same name, a different
/// operation, and an arity mismatch that would otherwise have shipped as a latent bug. It is left
/// fail-closed and named in `rholang_ast.rs::unsupported_construct_name`.
///
/// Each row uses EXACTLY the arity `lower_proc` emits, so a future edit that changes an argument
/// list fails here rather than in someone's program. Rows that answer an observable value assert
/// it; rows whose result is a zipper or pathmap have no `RuntimeObservationValue` variant and are
/// asserted only to REDUCE (an arity or carrier fault is an `Err`, never an empty `Ok`).
#[tokio::test(flavor = "multi_thread")]
async fn c1b_routed_zipper_family_matches_the_interpreter_arity() {
    let pathmap = four_leaf_pathmap;
    let read_zipper = || zipper_method("readZipper", pathmap(), Vec::new());
    let write_zipper = || zipper_method("writeZipper", pathmap(), Vec::new());
    let segment = || zipper_elist(vec![zipper_gstring("b")]);
    let one = || zipper_expr_par(ZExprInstance::GInt(1));

    // ① Rows with an OBSERVABLE answer — arity *and* meaning are pinned.
    for (label, call, expected) in [
        ("leafCount/0", zipper_method("leafCount", read_zipper(), vec![]), "4"),
        // The root's children are the distinct first segments "a", "b", "c".
        ("childCount/0", zipper_method("childCount", read_zipper(), vec![]), "3"),
        // Leaf 3 of the documented depth-first order is `["b"]`, and a PathMap element is both key
        // and value, so `getLeaf` answers the same list `getPath` does.
        ("getLeaf/0", zipper_method("getLeaf", leaf_walk(3), vec![]), r#"["b"]"#),
        ("getPath/0", zipper_method("getPath", leaf_walk(1), vec![]), r#"["a", "x"]"#),
    ] {
        let observed = reduce_expression(call)
            .await
            .unwrap_or_else(|err| panic!("C1b {label}: must reduce, got {err}"));
        assert_eq!(
            observed.iter().map(render_as_rholang).collect::<Vec<_>>(),
            vec![expected.to_string()],
            "C1b {label}: the routed name/arity must reach the interpreter's own implementation"
        );
    }

    // ② Rows whose result is a zipper or a pathmap — no observation variant exists for either, so
    //    the assertion is that the call REDUCES. An arity fault
    //    (`MethodArgumentNumberMismatch`) or a carrier fault (`MethodNotDefined`) is an `Err`.
    for (label, call) in [
        ("getSubtrie/0(pathmap)", zipper_method("getSubtrie", pathmap(), vec![])),
        ("getSubtrie/0(zipper)", zipper_method("getSubtrie", read_zipper(), vec![])),
        ("readZipper/0", zipper_method("readZipper", pathmap(), vec![])),
        ("readZipperAt/1", zipper_method("readZipperAt", pathmap(), vec![segment()])),
        ("writeZipper/0", zipper_method("writeZipper", pathmap(), vec![])),
        ("writeZipperAt/1", zipper_method("writeZipperAt", pathmap(), vec![segment()])),
        ("descendTo/1", zipper_method("descendTo", read_zipper(), vec![segment()])),
        ("descendFirst/0", zipper_method("descendFirst", read_zipper(), vec![])),
        (
            "descendIndexedBranch/1",
            zipper_method("descendIndexedBranch", read_zipper(), vec![one()]),
        ),
        ("ascendOne/0", zipper_method("ascendOne", leaf_walk(3), vec![])),
        ("ascend/1", zipper_method("ascend", leaf_walk(3), vec![one()])),
        ("toNextLeaf/0", zipper_method("toNextLeaf", read_zipper(), vec![])),
        ("setSubtrie/1", zipper_method("setSubtrie", write_zipper(), vec![pathmap()])),
        ("removeLeaf/0", zipper_method("removeLeaf", write_zipper(), vec![])),
        ("removeBranches/0", zipper_method("removeBranches", write_zipper(), vec![])),
        ("graft/1", zipper_method("graft", write_zipper(), vec![read_zipper()])),
        ("joinInto/1", zipper_method("joinInto", write_zipper(), vec![read_zipper()])),
        // At the ROOT there is no sibling to move to; both are routed at arity 0 and answer
        // fail-soft rather than erroring. Recorded because that is the interpreter's choice, not
        // this lowering's, and it differs from `toNextLeaf`'s `Nil`.
        ("toNextSibling/0", zipper_method("toNextSibling", read_zipper(), vec![])),
        ("toPrevSibling/0", zipper_method("toPrevSibling", read_zipper(), vec![])),
    ] {
        let result = reduce_expression(call).await;
        assert!(
            result.is_ok(),
            "C1b {label}: the routed name/arity must be accepted by the interpreter. An \
             `ArgumentNumberMismatch` here means `lower_proc` emits the wrong argument list; a \
             `MethodNotDefined` means the name is not this operation's name. Got {result:?}"
        );
    }
}

// ════════════════════════════════════════════════════════════════════════════════════════════════
// C4 — THE NATIVE HOMOGENEOUS PATHMAP CARRIER
// ════════════════════════════════════════════════════════════════════════════════════════════════
//
// C4 is closed with one discriminated representation, not a mixed entry list:
// neutral empty makes no premature choice; set mode is `PathMap<()>`; and map
// mode is `PathMap<Par>`. Both concrete modes keep canonical compressed byte
// keys and serialize as the native EPM1 snapshot.

/// **★ C4-1 — set mode remains the key-as-member specialization.**
///
/// In `PathMap<()>` there is deliberately no duplicate `Par` value. A present
/// member reads back from its canonical key. Map mode, tested separately below,
/// retains values distinct from their keys.
#[tokio::test(flavor = "multi_thread")]
async fn c4_set_specialization_reads_each_member_from_its_canonical_key() {
    // ① `getPath() == getLeaf()` at every set leaf.
    for steps in 1..=4usize {
        let key_is_value = zipper_expr_par(ZExprInstance::EEqBody(ZEEq {
            p1: Some(zipper_method("getPath", leaf_walk(steps), Vec::new())),
            p2: Some(zipper_method("getLeaf", leaf_walk(steps), Vec::new())),
        }));
        let observed = reduce_expression(key_is_value)
            .await
            .unwrap_or_else(|err| panic!("leaf {steps}: the comparison must reduce: {err}"));
        assert_eq!(
            observed.iter().map(render_as_rholang).collect::<Vec<_>>(),
            vec!["true".to_string()],
            "C4-1: at set leaf {steps}, membership is represented by PathMap<()>"
        );
    }

    // ② `atPath(k)` answers `k` — the lookup returns the key, because the key is the value.
    let observed = reduce_expression(zipper_method(
        "atPath",
        four_leaf_pathmap(),
        vec![zipper_elist(vec![zipper_gstring("b")])],
    ))
    .await
    .expect("atPath on the native carrier reduces");
    assert_eq!(
        observed.iter().map(render_as_rholang).collect::<Vec<_>>(),
        vec![r#"["b"]"#.to_string()],
        "C4-1: set-mode `atPath` decodes the present member key"
    );
}

/// **★ C4-2 — map mode preserves distinct keys and values on native methods.**
///
/// The key and value deliberately differ. Chaining `set`, `get`, and zipper
/// `leafCount` proves both value retention and carrier retention: an accidental
/// conversion to `EMap` would fail the following zipper dispatch.
#[tokio::test(flavor = "multi_thread")]
async fn c4_map_specialization_preserves_distinct_values_and_native_methods() {
    let one = || zipper_expr_par(ZExprInstance::GInt(1));
    let ten = || zipper_expr_par(ZExprInstance::GInt(10));
    let two = || zipper_expr_par(ZExprInstance::GInt(2));
    let twenty = || zipper_expr_par(ZExprInstance::GInt(20));
    let base = || zipper_epathmap_map(vec![(one(), ten())]);

    for (label, call, expected) in [
        ("get", zipper_method("get", base(), vec![one()]), "10"),
        ("contains", zipper_method("contains", base(), vec![one()]), "true"),
        ("size", zipper_method("size", base(), Vec::new()), "1"),
        (
            "set then get",
            zipper_method("get", zipper_method("set", base(), vec![two(), twenty()]), vec![two()]),
            "20",
        ),
        (
            "set stays pathmap",
            zipper_method(
                "leafCount",
                zipper_method(
                    "readZipper",
                    zipper_method("set", base(), vec![two(), twenty()]),
                    Vec::new(),
                ),
                Vec::new(),
            ),
            "2",
        ),
    ] {
        let observed = reduce_expression(call)
            .await
            .unwrap_or_else(|error| panic!("C4-2 {label}: {error}"));
        assert_eq!(
            observed.iter().map(render_as_rholang).collect::<Vec<_>>(),
            vec![expected.to_string()],
            "C4-2 {label}: map-mode EPathMap must retain key/value semantics"
        );
    }
}

/// **★ C4-3 — set-mode `setLeaf` inserts membership; map-mode writes the focused value.**
///
/// This fixture is deliberately set-specialized, so its one-argument `setLeaf`
/// cannot manufacture a key/value pair: it inserts the supplied member under
/// that member's canonical key. Map-mode focus replacement is covered by the
/// target zipper specifications; keeping the modes explicit prevents either
/// behavior from being generalized incorrectly to the other specialization.
#[tokio::test(flavor = "multi_thread")]
async fn c4_set_mode_set_leaf_adds_membership_independent_of_focus() {
    let new_element = || zipper_elist(vec![zipper_gstring("z")]);
    let write_at = |segment: &str| {
        zipper_method(
            "writeZipperAt",
            four_leaf_pathmap(),
            vec![zipper_elist(vec![zipper_gstring(segment)])],
        )
    };
    let after = |segment: &str| zipper_method("setLeaf", write_at(segment), vec![new_element()]);
    let count_of = |map: Par| zipper_method("leafCount", map, Vec::new());
    let rendered = |values: Vec<RuntimeObservationValue>| {
        values.iter().map(render_as_rholang).collect::<Vec<_>>()
    };

    // ① The map GREW. A focus-write would have replaced the entry at `["b"]` and left the count at
    //    four; an append adds a fifth.
    let observed = reduce_expression(count_of(after("b")))
        .await
        .expect("setLeaf reduces");
    assert_eq!(
        rendered(observed),
        vec!["5".to_string()],
        "C4-3: `setLeaf` must ADD an entry (4 → 5). A count of 4 would mean it overwrote the focus."
    );

    // ② The focused entry SURVIVED, and the new element landed at ITS OWN path — not at the focus.
    for (label, path, expected) in [
        ("the focused entry survives", "b", r#"["b"]"#),
        ("the new element is at its own path", "z", r#"["z"]"#),
    ] {
        let observed = reduce_expression(zipper_method(
            "atPath",
            after("b"),
            vec![zipper_elist(vec![zipper_gstring(path)])],
        ))
        .await
        .unwrap_or_else(|err| panic!("C4-3 {label}: must reduce: {err}"));
        assert_eq!(
            rendered(observed),
            vec![expected.to_string()],
            "C4-3 {label}: the write is addressed by the ELEMENT, never by the focus"
        );
    }

    // ③ ★ THE REFUTATION OF THE PROPOSED REWRITE. Two DIFFERENT foci produce the SAME map, and
    //    both equal the no-zipper form. `writeZipperAt(p)` is inert in front of `setLeaf`.
    for (label, left, right) in [
        ("two different foci agree", after("b"), after("c")),
        (
            "a focus agrees with no zipper at all",
            after("b"),
            zipper_method(
                "setLeaf",
                zipper_method("writeZipper", four_leaf_pathmap(), Vec::new()),
                vec![new_element()],
            ),
        ),
    ] {
        let same =
            zipper_expr_par(ZExprInstance::EEqBody(ZEEq { p1: Some(left), p2: Some(right) }));
        let observed = reduce_expression(same)
            .await
            .unwrap_or_else(|err| panic!("C4-3 {label}: the comparison must reduce: {err}"));
        assert_eq!(
            rendered(observed),
            vec!["true".to_string()],
            "C4-3 {label}: if this were `false`, `setLeaf` WOULD honour the focus and the C1b \
             rewrite `writeZipperAt(full).setLeaf(v)` would be sound. It is `true`, so the rewrite \
             is a silent no-op on the path and must never be shipped."
        );
    }

    // ④ And the arity really is one — the half of the C1b record that was right.
    let error = reduce_expression(zipper_method(
        "setLeaf",
        zipper_method("writeZipper", four_leaf_pathmap(), Vec::new()),
        vec![zipper_elist(vec![zipper_gstring("b")]), new_element()],
    ))
    .await
    .expect_err("Rholang's two-argument setLeaf has no counterpart");
    assert!(
        error.contains(
            r#"MethodArgumentNumberMismatch { method: "setLeaf", expected: 1, actual: 2 }"#
        ),
        "C4-3: the interpreter's `setLeaf` takes exactly one argument. Got {error}"
    );
}

/// **★ C4-4 — `restrict` is NOT `restriction`; exact intersection and prefix restriction differ.**
///
/// C1b left all three fail-closed with "plausible but not verified counterparts … could not be
/// exercised against the reducer even once". The premise was wrong — a real `EPathMap` is
/// constructible right here, which is how this test exists — and so was the guess.
///
/// | Rholang (`runtime/src/pathmap_bridge.rs`) | keys kept | values kept |
/// |---|---|---|
/// | `restrict(base, mask)` (`trie_restrict_lit`) | base keys **exactly present** in mask | base's |
/// | `meet(left, right)` (`trie_meet_lit`) | left keys **exactly present** in right | right's |
///
/// | Rholang (`reduce.rs`) | keys kept |
/// |---|---|
/// | `restriction` (4666) | base keys **under a PREFIX** in other (`PathMap::restrict`, non-terminated keys) |
/// | `intersection` (4589) | base keys **exactly present** in other (`PathMap::meet`) |
///
/// So `restrict` ↦ `restriction` is a mis-mapping: it would silently widen exact membership into
/// prefix containment. The set-mode fixture below isolates that topology
/// distinction. Map-mode value provenance is tested by the target's native
/// EPathMap algebra suite, where `PathMap<Par>` makes it observable.
#[tokio::test(flavor = "multi_thread")]
async fn c4_restrict_is_not_restriction_and_meet_is_intersection() {
    // base = {["a","x"], ["a","y"], ["b"]}; mask = {["a"], ["c"]} — `["a"]` is a strict PREFIX of
    // two base entries and an exact match for none. That is the whole discriminator.
    let base = || {
        zipper_epathmap(vec![
            zipper_elist(vec![zipper_gstring("a"), zipper_gstring("x")]),
            zipper_elist(vec![zipper_gstring("a"), zipper_gstring("y")]),
            zipper_elist(vec![zipper_gstring("b")]),
        ])
    };
    let prefix_mask = || {
        zipper_epathmap(vec![
            zipper_elist(vec![zipper_gstring("a")]),
            zipper_elist(vec![zipper_gstring("c")]),
        ])
    };
    let exact_mask = || {
        zipper_epathmap(vec![
            zipper_elist(vec![zipper_gstring("a"), zipper_gstring("x")]),
            zipper_elist(vec![zipper_gstring("c")]),
        ])
    };

    for (label, call, expected_count) in [
        // PREFIX mask: `restriction` keeps both entries under `["a"]` …
        (
            "restriction/prefix",
            zipper_method("restriction", base(), vec![prefix_mask()]),
            "2",
        ),
        // … while `intersection` keeps NONE, because `["a"]` is not itself an entry of base.
        (
            "intersection/prefix",
            zipper_method("intersection", base(), vec![prefix_mask()]),
            "0",
        ),
        // EXACT mask: the two coincide, which is why an exact-only fixture could never have caught
        // the difference.
        (
            "restriction/exact",
            zipper_method("restriction", base(), vec![exact_mask()]),
            "1",
        ),
        (
            "intersection/exact",
            zipper_method("intersection", base(), vec![exact_mask()]),
            "1",
        ),
    ] {
        let observed = reduce_expression(zipper_method("leafCount", call, Vec::new()))
            .await
            .unwrap_or_else(|err| panic!("C4-4 {label}: must reduce: {err}"));
        assert_eq!(
            observed.iter().map(render_as_rholang).collect::<Vec<_>>(),
            vec![expected_count.to_string()],
            "C4-4 {label}: `restriction` is PREFIX containment and `intersection` is EXACT \
             membership. Rholang's `restrict` is exact, so `restriction` is the WRONG target."
        );
    }

    // The surviving entry under the exact mask is the same one on both operators — set-mode
    // key-level agreement.
    for method in ["restriction", "intersection"] {
        let observed = reduce_expression(zipper_method(
            "atPath",
            zipper_method(method, base(), vec![exact_mask()]),
            vec![zipper_elist(vec![zipper_gstring("a"), zipper_gstring("x")])],
        ))
        .await
        .unwrap_or_else(|err| panic!("C4-4 {method}: atPath must reduce: {err}"));
        assert_eq!(
            observed.iter().map(render_as_rholang).collect::<Vec<_>>(),
            vec![r#"["a", "x"]"#.to_string()],
            "C4-4 {method}: the kept entry is the common key"
        );
    }
}

/// **★ C4-5 — `getSubtrieAt(p)` IS `readZipperAt(p).getSubtrie()`, and the result keeps ABSOLUTE
/// paths.**
///
/// C1b recorded that composing `getSubtrie` with `atPath` "is a semantic claim of the same
/// untestable kind" as `restrict`/`meet`. It is testable, the composition is not with `atPath` (a
/// value lookup) but with `readZipperAt` (a focus move), and the composition's exact shape matters:
/// the returned subtrie carries the entries' FULL paths, not paths relative to `p`. A caller that
/// assumed relative paths would index one segment short on every entry.
///
/// A miss is the EMPTY pathmap, not an error — the carrier's established fail-soft, and the same
/// convention `readZipperAt` at a missing prefix already uses.
#[tokio::test(flavor = "multi_thread")]
async fn c4_get_subtrie_at_is_read_zipper_at_then_get_subtrie() {
    let subtrie_at = |segment: &str| {
        zipper_method(
            "getSubtrie",
            zipper_method(
                "readZipperAt",
                four_leaf_pathmap(),
                vec![zipper_elist(vec![zipper_gstring(segment)])],
            ),
            Vec::new(),
        )
    };

    for (label, segment, expected_count) in [
        ("branch", "a", "2"),
        ("leaf", "b", "1"),
        ("miss is fail-soft, not an error", "zz", "0"),
    ] {
        let observed =
            reduce_expression(zipper_method("leafCount", subtrie_at(segment), Vec::new()))
                .await
                .unwrap_or_else(|err| panic!("C4-5 {label}: must reduce: {err}"));
        assert_eq!(
            observed.iter().map(render_as_rholang).collect::<Vec<_>>(),
            vec![expected_count.to_string()],
            "C4-5 {label}: `readZipperAt({segment:?}).getSubtrie()` scopes to the branch"
        );
    }

    // ★ ABSOLUTE, not relative: the subtrie under `["a"]` is addressed by `["a","x"]`, and NOT by
    //   the relative `["x"]`.
    let observed = reduce_expression(zipper_method(
        "atPath",
        subtrie_at("a"),
        vec![zipper_elist(vec![zipper_gstring("a"), zipper_gstring("x")])],
    ))
    .await
    .expect("C4-5: the absolute address must reduce");
    assert_eq!(
        observed.iter().map(render_as_rholang).collect::<Vec<_>>(),
        vec![r#"["a", "x"]"#.to_string()],
        "C4-5: the subtrie retains ABSOLUTE paths — a caller expecting relative ones would be off \
         by the prefix on every entry"
    );
}

/// **★ C4-6 — a BARE element reads back AS ITSELF. The positive twin of a retired witness.**
///
/// ## What this replaced, and why the replacement is not a relaxation
///
/// Until 2026-07-27 this slot held `c4_defect_a_bare_element_reads_back_as_nil`, which asserted
/// that every VALUE read of a bare element answered `Nil`. That defect is FIXED, so the witness
/// would have been a check that can no longer fail; it is replaced here by the assertions it told
/// its reader to write, extended with an executable control (③ below) that reproduces the retired
/// behaviour on demand.
///
/// ## The defect that was
///
/// `create_pathmap_from_elements` keys an element by `canonical_path::encode_trie_path(par)`, whose
/// two arms are
///
/// ```text
///     split (a ground list [e1..ek])   key = enc(e1) ‖ … ‖ enc(ek) ‖ 0x00
///     bare  (anything else)            key = enc(par)                     ← NO terminator
/// ```
///
/// while every READER rebuilt the key as `segments_to_key(par_to_path(par), true)` — the same
/// segments with the terminator appended unconditionally, i.e. the split arm, always. The two agree
/// on a ground `EList` and disagree on every bare Par:
///
/// ```text
///     element      insert key (encode_trie_path)   read key (segments_to_key(_, true))
///     ────────     ─────────────────────────────   ───────────────────────────────────
///     1            0302                            030200          ✗ disagree
///     "p"          040170                          04017000        ✗ disagree
///     true         02                              0200            ✗ disagree
///     ["a"]        04016100                        04016100        ✓ agree
///     ["a","x"]    04016104017800                  04016104017800  ✓ agree
/// ```
///
/// ## ⚠ THE NARRATIVE THIS SLOT USED TO CARRY WAS WRONG — do not follow it
///
/// The retired witness offered two candidate fixes and called them "consensus-visible and therefore
/// presentable, not landable". **Both were refuted, and the fix that landed is neither.** A later
/// reader who starts from the old text starts from a dead path, which is why it is rewritten here
/// rather than annotated.
///
/// * ✗ *"key bare elements WITH the terminator"* — would have moved `encode_trie_path`, the
///   canonical key stream (`serialized_paths`, proto field 8) and the Blake2b hash preimage,
///   re-keying every ground map holding a bare element. It was also **insufficient**: `5aacebc3`
///   established that the walk's fixed point lives inside the walk primitive, so terminating the
///   key would have removed one trigger and left the others (`readZipperAt` on a miss, any
///   `descendTo` into empty space).
/// * ✗ *"read with `terminate = false` for bare elements — the read side cannot tell them apart"* —
///   true only of a reader holding SEGMENTS. It is false of a reader holding the whole path as a
///   `Par`, and false of a cursor that is allowed to carry its own arm. The premise was the bug.
///
/// ## The three f1r3node commits that actually closed it
///
/// | # | commit | what it fixed | key stream |
/// |---|---|---|---|
/// | 2 | `5aacebc3` | `next_value_key` is total: the LEAST key strictly greater than `from_key`, for any `from_key`, existing or not | untouched |
/// | 3 | `0a6d2ce0` | `entry_key_at` — a reader holding the whole path `Par` asks the codec instead of rebuilding | untouched |
/// | 4-6 | `7dcff96f` | `EZipper.cursor_kind` (`RhoTypes.proto`) — the cursor carries `Split`/`Bare`/`Prefix`, and `cursor_entry_key` spends it | untouched |
///
/// Stage 2 is the one that shows how far off the old attribution was: the `toNextLeaf` fixed point
/// was an upstream pathmap-0.2.2 iteration bug (`DenseByteNode::iter_token_for_path` returns the
/// node's FULL child mask when the dangling key is longer than one byte, silently REWINDING to that
/// node's first child), and not a key-termination problem at all. It also explains why the defect
/// looked shape-dependent — `LineListNode`'s twin compares the whole key and does not rewind, so
/// two-entry tries advanced and three-entry tries did not.
///
/// ★ **No canonical key moved and no activation height was needed.** All three commits are
/// explicit that `create_pathmap_from_elements`, `encode_trie_path` and `path_stream_of` are
/// untouched; `cursor_kind` is ADDITIVE with `Split == 0`, and prost omits a default-valued scalar,
/// so `ezipper.prost.bin` is byte-identical and every zipper serialized before the field existed
/// decodes to exactly the prior semantics. The consensus-commitment framing the witness used to
/// hold this behind never applied to the fix that was available.
#[tokio::test(flavor = "multi_thread")]
async fn c4_a_bare_element_reads_back_as_itself() {
    // ① The map, its count, and the BARE cursor the walk lands on. `getPath()` answers the element
    //    `1` and NOT the singleton list `[1]`: those are different entries that one map may hold at
    //    once, and reporting the wrong one was the defect, not a rendering choice.
    for (label, call, expected) in [
        ("leafCount", zipper_method("leafCount", bare_element_pathmap(), Vec::new()), "3"),
        (
            "getPath",
            zipper_method(
                "getPath",
                walk_from(zipper_method("readZipper", bare_element_pathmap(), Vec::new()), 1),
                Vec::new(),
            ),
            "1",
        ),
    ] {
        let observed = reduce_expression(call)
            .await
            .unwrap_or_else(|err| panic!("C4-6 {label}: must reduce: {err}"));
        assert_eq!(
            observed.iter().map(render_as_rholang).collect::<Vec<_>>(),
            vec![expected.to_string()],
            "C4-6 {label}: the cursor names the BARE entry — `[1]` here is the singleton LIST, a \
             different entry"
        );
    }

    // ② Every set-mode VALUE read answers the member. In `PathMap<()>`, `getLeaf()` at a stop
    //    decodes the present key and `atPath(k)` returns that member.
    for steps in 1..=3usize {
        let expected = steps.to_string();
        let observed = reduce_expression(zipper_method(
            "getLeaf",
            walk_from(zipper_method("readZipper", bare_element_pathmap(), Vec::new()), steps),
            Vec::new(),
        ))
        .await
        .unwrap_or_else(|err| panic!("C4-6 getLeaf at step {steps}: must reduce: {err}"));
        assert_eq!(
            observed.iter().map(render_as_rholang).collect::<Vec<_>>(),
            vec![expected.clone()],
            "C4-6 getLeaf at step {steps}: the walk's own cursor must read its element back"
        );

        let observed = reduce_expression(zipper_method(
            "atPath",
            bare_element_pathmap(),
            vec![zipper_expr_par(ZExprInstance::GInt(steps as i64))],
        ))
        .await
        .unwrap_or_else(|err| panic!("C4-6 atPath({steps}): must reduce: {err}"));
        assert_eq!(
            observed.iter().map(render_as_rholang).collect::<Vec<_>>(),
            vec![expected],
            "C4-6 atPath({steps}): the BARE key addresses the entry it was inserted under"
        );
    }

    // ③ ★ ANTI-VACUITY — the retired behaviour, RUN. `readZipperAt` given a ground-LIST argument
    //    produces a `Split` cursor, and `par_to_path` gives the bare element `1` and the singleton
    //    list `[1]` the SAME segment vector. So `readZipperAt([1])` on this map is exactly the
    //    pre-fix cursor: identical segments, arm guessed as split. `cursor_entry_key(segs, Split, m)
    //    == segments_to_key(segs, true)` BY CONSTRUCTION, so its reads run the byte-identical
    //    expression `7dcff96f^` ran unconditionally — and they still answer the pre-fix values.
    //
    //    This is what keeps ② from being a check that cannot fail: ② and ③ differ ONLY in the
    //    cursor's arm, so if the discriminator were dropped, every row of ② would collapse onto ③.
    let split_cursor_at_one = || {
        zipper_method(
            "readZipperAt",
            bare_element_pathmap(),
            vec![zipper_elist(vec![zipper_expr_par(ZExprInstance::GInt(1))])],
        )
    };
    let observed = reduce_expression(zipper_method("getPath", split_cursor_at_one(), Vec::new()))
        .await
        .expect("C4-6 pre-fix control: getPath must reduce");
    assert_eq!(
        observed.iter().map(render_as_rholang).collect::<Vec<_>>(),
        vec!["[1]".to_string()],
        "C4-6 pre-fix control: a SPLIT cursor over the same segments reports the LIST — this is \
         the exact value the retired witness asserted for the walk's own cursor"
    );
    let observed = reduce_expression(reads_as_nil(zipper_method(
        "getLeaf",
        split_cursor_at_one(),
        Vec::new(),
    )))
    .await
    .expect("C4-6 pre-fix control: the Nil comparison must reduce");
    assert_eq!(
        observed.iter().map(render_as_rholang).collect::<Vec<_>>(),
        vec!["true".to_string()],
        "C4-6 pre-fix control: the split key `030200` is not in this map, so the guessing reader \
         still answers Nil. If THIS ever flips, the arm stopped being spent and ② is vacuous"
    );

    // ④ The same statement from the argument side, and it is a semantic row as well as a control:
    //    `[1]` is genuinely NOT an entry of `{| 1, 2, 3 |}`, and the pre-fix reader computed this
    //    very key for the bare `1`.
    let observed = reduce_expression(reads_as_nil(zipper_method(
        "atPath",
        bare_element_pathmap(),
        vec![zipper_elist(vec![zipper_expr_par(ZExprInstance::GInt(1))])],
    )))
    .await
    .expect("C4-6: the one-segment list comparison must reduce");
    assert_eq!(
        observed.iter().map(render_as_rholang).collect::<Vec<_>>(),
        vec!["true".to_string()],
        "C4-6: `atPath([1])` must MISS — the bare `1` and the list `[1]` are different entries, and \
         conflating them is what `entry_key_at` removed"
    );

    // ⑤ The ground-list control, unchanged from the witness: the very same reads answer correctly
    //    on the other element shape, which is what localises every claim above to the bare arm.
    let observed = reduce_expression(zipper_method(
        "atPath",
        four_leaf_pathmap(),
        vec![zipper_elist(vec![zipper_gstring("b")])],
    ))
    .await
    .expect("C4-6 control: must reduce");
    assert_eq!(
        observed.iter().map(render_as_rholang).collect::<Vec<_>>(),
        vec![r#"["b"]"#.to_string()],
        "C4-6 control: a GROUND-LIST element still reads back through the split arm — the fix moved \
         ZERO bytes on this shape"
    );
}

/// **★ C4-7 — a SUBTRIE walk is bounded by the COUNT, never by `Nil`. `toNextLeaf` leaves the
/// branch.**
///
/// Found by extending [`c1_zipper_walk_exhaustion_terminates_within_leaf_count`] to a non-root
/// focus: the added row asserted that a walk from `readZipperAt(["a"])` becomes `Nil` at that
/// branch's `leafCount() + 1 = 3`. **It failed**, and the failure is the result — measured, step by
/// step, below.
///
/// ```text
///     m = {| ["a","x"], ["a","y"], ["b"], ["c","z"] |}
///     z = m.readZipperAt(["a"])        z.leafCount() == 2      ← BRANCH-scoped
///
///     step   z.getPath()      in the branch?     z == Nil ?
///     ────   ─────────────    ──────────────     ──────────
///       1    ["a", "x"]       ✔                  false
///       2    ["a", "y"]       ✔                  false
///       3    ["b"]            ✘  ESCAPED         false      ← the trap
///       4    ["c", "z"]       ✘  ESCAPED         false
///       5    —                                   true       ← the WHOLE MAP's count + 1
/// ```
///
/// Both facts are correct in isolation and both are already pinned: `leafCount()` is subtrie-scoped
/// (`zipper_enumeration_spec.rs::leaf_count_is_the_walk_bound` asserts `2` at `["a"]`), and the
/// first `leafCount()` steps do stay in the branch, because prefix-sharing keys are contiguous in
/// depth-first order (`scoped_enumeration_is_algebraic`, and mettail's
/// `zipper.rs::leaf_walk_from_a_strict_prefix_stays_in_the_branch`). What neither side had measured
/// is what happens on the step AFTER: the walk does not stop, it continues into the rest of the
/// map. Both specs stop at exactly `n` steps, so the escape was never observed.
///
/// ⚠ **The consequence for the counted-walk idiom.** At the ROOT, `leafCount()` and the `Nil`
/// sentinel agree, so either may be used to terminate. **At a prefix they do not**, and only the
/// count is sound:
///
/// * `n` steps then stop  — correct, and scoped to the branch;
/// * walk until `Nil`     — reads the whole map from `["a"]` onward, silently, with no error
///   anywhere. That is the same silent-wrongness class as the exhaustion mistranslation, reached
///   from the other side: not a walk that never ends, but a walk that ends in the right place
///   having visited the wrong entries.
///
/// The scoped alternative that IS `Nil`-terminable is the algebraic one — `getSubtrie()` first,
/// then `readZipper()` over the branch as a map in its own right, whose exhaustion really is the
/// branch's end. That is measured here too, so the safe idiom is recorded beside the trap.
#[tokio::test(flavor = "multi_thread")]
async fn c4_a_subtrie_walk_is_bounded_by_the_count_not_by_nil() {
    let at_a = || {
        zipper_method(
            "readZipperAt",
            four_leaf_pathmap(),
            vec![zipper_elist(vec![zipper_gstring("a")])],
        )
    };

    // ① The bound really is branch-scoped: 2, not the map's 4.
    let counted = reduce_expression(zipper_method("leafCount", at_a(), Vec::new()))
        .await
        .expect("leafCount at the prefix reduces");
    assert_eq!(
        counted.iter().map(render_as_rholang).collect::<Vec<_>>(),
        vec!["2".to_string()],
        "C4-7: `leafCount()` at `[\"a\"]` counts the BRANCH"
    );

    // ② Step by step: the first two stay in, the next two ESCAPE, and `Nil` arrives only at the
    //    whole map's count + 1.
    for (steps, expected_path) in [
        (1usize, r#"["a", "x"]"#),
        (2, r#"["a", "y"]"#),
        (3, r#"["b"]"#),
        (4, r#"["c", "z"]"#),
    ] {
        let observed =
            reduce_expression(zipper_method("getPath", walk_from(at_a(), steps), vec![]))
                .await
                .unwrap_or_else(|err| panic!("C4-7 step {steps}: must reduce: {err}"));
        assert_eq!(
            observed.iter().map(render_as_rholang).collect::<Vec<_>>(),
            vec![expected_path.to_string()],
            "C4-7 step {steps}: steps 3 and 4 are OUTSIDE the branch — that is the trap. If this \
             ever reports `Nil` or an error at step 3, the walk became branch-scoped and this test \
             must be replaced by the (better) branch-terminating contract."
        );

        let is_nil = reduce_expression(walk_from_is_nil(at_a(), steps))
            .await
            .unwrap_or_else(|err| panic!("C4-7 step {steps}: the Nil test must reduce: {err}"));
        assert_eq!(
            is_nil.iter().map(render_as_rholang).collect::<Vec<_>>(),
            vec!["false".to_string()],
            "C4-7 step {steps}: `Nil` is NOT the branch sentinel — a walk-until-Nil from a prefix \
             does not stop at the branch boundary"
        );
    }

    // ③ Exhaustion lands at the WHOLE MAP's cardinality + 1 = 5, not at the branch's 2 + 1 = 3.
    let is_nil = reduce_expression(walk_from_is_nil(at_a(), 5))
        .await
        .expect("the fifth step's Nil test reduces");
    assert_eq!(
        is_nil.iter().map(render_as_rholang).collect::<Vec<_>>(),
        vec!["true".to_string()],
        "C4-7: the walk from a prefix is MAP-scoped — it exhausts at the map's count + 1"
    );

    // ④ The SAFE idiom: scope algebraically first. `getSubtrie()` yields the branch as a map in its
    //    own right, and THAT map's walk exhausts at the branch's own count + 1.
    let branch =
        || zipper_method("readZipper", zipper_method("getSubtrie", at_a(), Vec::new()), Vec::new());
    for (steps, expected) in [(1usize, "false"), (2, "false"), (3, "true")] {
        let observed = reduce_expression(walk_from_is_nil(branch(), steps))
            .await
            .unwrap_or_else(|err| panic!("C4-7 safe idiom step {steps}: must reduce: {err}"));
        assert_eq!(
            observed.iter().map(render_as_rholang).collect::<Vec<_>>(),
            vec![expected.to_string()],
            "C4-7 safe idiom: `getSubtrie().readZipper()` IS `Nil`-terminable at the branch \
             boundary — this is the enumeration to reach for when the bound is not carried"
        );
    }
}

/// **★★ C4-8 — over BARE elements the leaf walk visits every element, in order, and STOPS.**
///
/// The positive twin of `c4_defect_a_bare_element_walk_never_advances`, which held this slot until
/// 2026-07-27 and asserted the exact opposite at six consecutive steps. That witness had told its
/// reader what to do when the walk was fixed — restore the bare row to
/// [`c1_zipper_walk_exhaustion_terminates_within_leaf_count`], which is where it was written — and
/// the row IS restored there. What remains here is the part that row does not carry: the per-step
/// VALUES, which are the direct positive image of the witness's parked table.
///
/// ```text
///     RETIRED WITNESS (measured 2026-07-26)          NOW (measured 2026-07-27)
///     step  1  2  3  4  5  6                         step  1  2  3  4
///     path [1][1][1][1][1][1]  ← never moves         path  1  2  3  ✗ raises
///     Nil?  F  F  F  F  F  F   ← never exhausts      Nil?  F  F  F  true
/// ```
///
/// ⚠ **Six steps were needed to tell those two apart, and one was not.** At step 1 alone the move
/// is `["[1]"]` → `["1"]`, which is equally consistent with *"still parked, only the RENDERING
/// changed"* — the walk staying on the first leaf while `getPath` learned to report the bare
/// element instead of the singleton list. Only enumerating the whole bound distinguishes a walk
/// that moved from a walk that was re-rendered, and both halves DID move here: the paths are bare
/// AND they advance.
///
/// ## What actually fixed it — and it is not what the witness predicted
///
/// The witness attributed the fixed point to key termination: *"`from_key` is ALWAYS terminated, a
/// bare element's stored key is NOT, so `move_to_path` lands on a path that has no node and the
/// recovery `to_next_val()` re-selects the FIRST value."* The symptom was right and the cause was
/// not. f1r3node `5aacebc3` measured the fixed point INSIDE the walk primitive, in pathmap-0.2.2:
/// `ReadZipperCore::to_next_get_val` opens iteration with `iter_token_for_path(node_key())`, and
/// `DenseByteNode::iter_token_for_path` answers with the node's FULL child mask whenever that key
/// is longer than one byte — i.e. it REWINDS to the node's first child. Any focus dangling two or
/// more bytes past the deepest existing node triggers it, so terminating the key would have removed
/// one trigger and left `readZipperAt` on a miss and every `descendTo` into empty space.
///
/// `next_value_key` replaces it with an ORDER property — *the least key in the map strictly greater
/// than `from_key`, or `None`* — which is total, needs `from_key` neither to exist nor to prefix
/// anything, and never asks the crate to iterate from a dangling focus. The rest of the cluster
/// (the `Nil` value reads, and `getPath` reporting the list) is `0a6d2ce0` + `7dcff96f`; the full
/// three-commit derivation is on [`c4_a_bare_element_reads_back_as_itself`].
///
/// ## ⚠ The Rholang consequence, which was the whole reason this mattered
///
/// Rholang pathmap keys are BARE by default — `{| 1 : 10 |}` has key `1`, and
/// `encode_proc_path_entry` gives a bare `Proc` one segment. The witness recorded that pointing
/// `lower_pathmap` at `EPathmapBody` would therefore make the enumeration surface C4 exists to
/// unlock HANG rather than work. **That blocker is gone.** What still blocks C4 is the carrier's
/// missing VALUE SLOT, and only that — see
/// [`divergence_g_target_pathmap_and_zippers_use_their_native_carriers`].
///
/// ⚠ **STILL BOUNDED BY CONSTRUCTION.** Every step below is a fixed, small number; nothing here can
/// hang however the walk behaves.
#[tokio::test(flavor = "multi_thread")]
async fn c4_a_bare_element_walk_visits_every_element_in_order() {
    let root = || zipper_method("readZipper", bare_element_pathmap(), Vec::new());

    // The bound the carrier advertises, and now also the number of steps the walk takes.
    let counted = reduce_expression(zipper_method("leafCount", root(), Vec::new()))
        .await
        .expect("leafCount reduces");
    assert_eq!(
        counted.iter().map(render_as_rholang).collect::<Vec<_>>(),
        vec!["3".to_string()],
        "C4-8: the map holds three entries, and a counted walk over it now reads three DISTINCT \
         ones"
    );

    // ① The per-step values: byte-lex order over the bare keys, each element reported bare.
    for (steps, expected_path) in [(1usize, "1"), (2, "2"), (3, "3")] {
        let path = reduce_expression(zipper_method("getPath", walk_from(root(), steps), vec![]))
            .await
            .unwrap_or_else(|err| panic!("C4-8 step {steps}: getPath must reduce: {err}"));
        assert_eq!(
            path.iter().map(render_as_rholang).collect::<Vec<_>>(),
            vec![expected_path.to_string()],
            "C4-8 step {steps}: the walk must ADVANCE, and must report the BARE element. `[{}]` \
             here would be the retired fixed point wearing a new rendering",
            expected_path
        );

        let is_nil = reduce_expression(walk_from_is_nil(root(), steps))
            .await
            .unwrap_or_else(|err| panic!("C4-8 step {steps}: the Nil test must reduce: {err}"));
        assert_eq!(
            is_nil.iter().map(render_as_rholang).collect::<Vec<_>>(),
            vec!["false".to_string()],
            "C4-8 step {steps}: an entry the count promised must not be exhausted early"
        );
    }

    // ② And it STOPS — at exactly `leafCount() + 1`, which is what makes `walk until Nil` a
    //    terminating idiom over this element shape. The accessor on that sentinel fails closed;
    //    both facts, and why they are not in conflict, are pinned by
    //    [`c1_zipper_walk_cannot_continue_past_exhaustion`].
    let is_nil = reduce_expression(walk_from_is_nil(root(), 4))
        .await
        .expect("C4-8: the exhaustion test at leafCount() + 1 must reduce");
    assert_eq!(
        is_nil.iter().map(render_as_rholang).collect::<Vec<_>>(),
        vec!["true".to_string()],
        "C4-8: `walk until Nil` over a bare-element pathmap TERMINATES — this is the assertion the \
         retired witness recorded as false at six consecutive steps"
    );
}

/// ★★ **Every float arithmetic arm answers IEEE-754, and the case set is DERIVED from the
/// standard rather than transcribed from a list.** RULED 2026-07-29, extending the `Div` ruling to
/// the three siblings.
///
/// ## The derivation
///
/// IEEE 754-2019 §7.2 enumerates the *invalid operations*: for the four basic arithmetic
/// operations on a binary format, exactly these produce `NaN` from non-`NaN` operands —
///
/// | operation | §7.2 invalid cases | reachable in Rholang? |
/// |---|---|---|
/// | `+` | `(+∞) + (−∞)`, `(−∞) + (+∞)` | yes |
/// | `−` | `(+∞) − (+∞)`, `(−∞) − (−∞)` | yes |
/// | `×` | `0 × ±∞`, `±∞ × 0` (either signed zero) | yes |
/// | `÷` | `0 ÷ 0`, `±∞ ÷ ±∞` | yes |
/// | `REM` | `x REM 0`, `±∞ REM y` | **no** — see below |
/// | `√`  | negative operand | **no** — Rholang has no float `sqrt` |
///
/// §6.2 adds *propagation*: an operation with a quiet-`NaN` operand delivers a quiet `NaN`. §6.3
/// adds that a `NaN`'s sign is not interpreted, so negation propagates it. §7.4 makes overflow
/// deliver `±∞` under the default rounding attribute — an ANSWER, not an error.
///
/// Cross-checked against the arm inventory instead of against a wish-list: `rg` for
/// `SafeArith>::safe_` in `languages/src/rholang.rs` returns fifteen call sites, of which exactly
/// FOUR are on `CanonicalFloat64` — `safe_add`, `safe_sub`, `safe_mul`, `safe_div` — and the `Neg`
/// rule's float arm is a fifth site that reached `safe_neg` *implicitly*, through the operator
/// rewrite. All five are covered below. `safe_rem`'s only site is `i64`, and Rholang's `Mod` has no
/// float arm at all, which is why `REM` is unreachable; upstream's `combine_mod` refuses
/// `(GDouble, GDouble)` outright, so the two agree without any change.
///
/// ## ⚠ Why every assertion below is on a VALUE
///
/// A test of the form "this must not be `error`" passes on a STUCK TERM, and a stuck term is
/// exactly what the second trap produces. `macros/src/gen/native/rust_code_rewrite.rs`
/// (`binop_to_safe_method`, `:206-215`) rewrites every `+`, `-`, `*`, `/` inside a `![ … ]` block
/// into `<_ as SafeArith>::safe_*(…)?` — including on raw `f64` — and the `?` short-circuits the
/// whole fold body, so the rule never fires and the redex survives. The `Neg` arm was in precisely
/// that state before this commit: `-(0.0 / 0.0)` folded to the unreduced `-NaN`. Only an assertion
/// on the rendered VALUE distinguishes the three outcomes.
#[tokio::test(flavor = "multi_thread")]
async fn every_float_arithmetic_arm_answers_ieee754_for_every_indeterminate_form() {
    // Two ways to name an infinity in the surface syntax, so the cases below do not all depend on
    // the one operator under test. `inf` is not a Float literal (`rholang.rs:342`'s pattern
    // requires digits), so an infinity has to be COMPUTED.
    const POS_INF: &str = "(float(1.0, 64) / float(0.0, 64))";
    const NEG_INF: &str = "(float(-1.0, 64) / float(0.0, 64))";
    const OVERFLOW_INF: &str = "(float(1e308, 64) * float(10.0, 64))";
    const NAN: &str = "(float(0.0, 64) / float(0.0, 64))";

    // ★ THE FLOOR, first: every building block above must itself be a VALUE. If `POS_INF` were a
    // stuck term, every row built from it would be testing nothing.
    for (source, expected) in [
        (POS_INF, "inf"),
        (NEG_INF, "-inf"),
        (OVERFLOW_INF, "inf"),
        (NAN, "NaN"),
        // ...and ordinary float arithmetic still computes, on all four operators.
        ("float(1.5, 64) + float(2.5, 64)", "4.0"),
        ("float(5.0, 64) - float(1.5, 64)", "3.5"),
        ("float(1.5, 64) * float(4.0, 64)", "6.0"),
        ("float(7.0, 64) / float(2.0, 64)", "3.5"),
        ("-float(2.5, 64)", "-2.5"),
    ] {
        assert_eq!(
            fold(&parse(source)).unwrap_or_else(|err| panic!("{source:?}: {err}")),
            expected,
            "★ FLOOR: {source:?} must be a VALUE — every case below is built out of these",
        );
    }

    let cases: Vec<(String, &str, &str)> = vec![
        // ── §7.2, addition: magnitude subtraction of infinities ──────────────────────────────
        (format!("{POS_INF} + {NEG_INF}"), "NaN", "+: (+Inf) + (-Inf)"),
        (format!("{NEG_INF} + {POS_INF}"), "NaN", "+: (-Inf) + (+Inf)"),
        // ...and the SAME-sign sums are NOT invalid; they are infinities.
        (format!("{POS_INF} + {POS_INF}"), "inf", "+: (+Inf) + (+Inf) is not invalid"),
        (format!("{NEG_INF} + {NEG_INF}"), "-inf", "+: (-Inf) + (-Inf) is not invalid"),
        // ── §7.2, subtraction: magnitude subtraction of infinities ───────────────────────────
        (format!("{POS_INF} - {POS_INF}"), "NaN", "-: (+Inf) - (+Inf)"),
        (format!("{NEG_INF} - {NEG_INF}"), "NaN", "-: (-Inf) - (-Inf)"),
        // ...and the OPPOSITE-sign differences are infinities.
        (format!("{POS_INF} - {NEG_INF}"), "inf", "-: (+Inf) - (-Inf) is not invalid"),
        (format!("{NEG_INF} - {POS_INF}"), "-inf", "-: (-Inf) - (+Inf) is not invalid"),
        // ── §7.2, multiplication: zero times infinity, BOTH orders, BOTH signed zeros ────────
        (format!("float(0.0, 64) * {POS_INF}"), "NaN", "*: 0 * (+Inf)"),
        (format!("{POS_INF} * float(0.0, 64)"), "NaN", "*: (+Inf) * 0"),
        (format!("float(0.0, 64) * {NEG_INF}"), "NaN", "*: 0 * (-Inf)"),
        (format!("{NEG_INF} * float(0.0, 64)"), "NaN", "*: (-Inf) * 0"),
        (format!("float(-0.0, 64) * {POS_INF}"), "NaN", "*: -0 * (+Inf)"),
        (format!("{POS_INF} * float(-0.0, 64)"), "NaN", "*: (+Inf) * -0"),
        // ── §7.2, division: the two the Div ruling already covered, via computed infinities ──
        (format!("{POS_INF} / {POS_INF}"), "NaN", "/: (+Inf) / (+Inf)"),
        (format!("{POS_INF} / {NEG_INF}"), "NaN", "/: (+Inf) / (-Inf)"),
        // ── §7.4 overflow: an ANSWER (±Inf), never a decline — on all three operators ────────
        (
            "float(1e308, 64) + float(1e308, 64)".to_string(),
            "inf",
            "+: overflow delivers +Inf",
        ),
        (
            "float(-1e308, 64) - float(1e308, 64)".to_string(),
            "-inf",
            "-: overflow delivers -Inf",
        ),
        (
            "float(1e308, 64) * float(10.0, 64)".to_string(),
            "inf",
            "*: overflow delivers +Inf",
        ),
        (
            "float(1e308, 64) * float(-10.0, 64)".to_string(),
            "-inf",
            "*: overflow delivers -Inf",
        ),
        // ── §6.2 propagation: a NaN operand poisons every operator ───────────────────────────
        (format!("{NAN} + float(1.0, 64)"), "NaN", "+: NaN + 1.0 propagates"),
        (format!("float(1.0, 64) + {NAN}"), "NaN", "+: 1.0 + NaN propagates"),
        (format!("float(1.0, 64) - {NAN}"), "NaN", "-: 1.0 - NaN propagates"),
        (format!("{NAN} - float(1.0, 64)"), "NaN", "-: NaN - 1.0 propagates"),
        (
            format!("{NAN} * float(0.0, 64)"),
            "NaN",
            "*: NaN * 0.0 propagates (it is NOT 0.0)",
        ),
        (format!("float(2.0, 64) * {NAN}"), "NaN", "*: 2.0 * NaN propagates"),
        (format!("{NAN} / float(1.0, 64)"), "NaN", "/: NaN / 1.0 propagates"),
        (format!("float(1.0, 64) / {NAN}"), "NaN", "/: 1.0 / NaN propagates"),
        // ── §6.3, and THE FOURTH ARM: negation propagates a NaN, and does not strand it ──────
        (
            format!("-{NAN}"),
            "NaN",
            "unary -: -NaN propagates (was a STUCK TERM before this commit)",
        ),
        (format!("-{POS_INF}"), "-inf", "unary -: -(+Inf) is -Inf"),
        (format!("-{NEG_INF}"), "inf", "unary -: -(-Inf) is +Inf"),
    ];

    for (source, expected, what) in cases {
        let folded =
            fold(&parse(&source)).unwrap_or_else(|err| panic!("{what} — {source:?}: {err}"));
        assert_eq!(
            folded, expected,
            "★★ {what}: must be the IEEE-754 VALUE {expected:?}, not {folded:?}.\n\
             `error` means an arm is still declining an indeterminate form; anything that still \
             looks like the input means the operator rewrite short-circuited the fold and left a \
             stuck term.",
        );
    }
}

/// ⚠ **The signed-zero cases, asserted — they are the CARRIER's divergence, not the operators'.**
///
/// `CanonicalFloat64::canonicalize` (`runtime/src/canonical_float.rs:35-42`) maps `-0.0` to `+0.0`
/// so that terms have a well-defined `Eq`/`Hash`/`Ord`, and it does so when the LITERAL is built:
/// `float(-0.0, 64)` parses to `FloatLit(0.0)`. `CanonicalFloat64::safe_neg` normalises the same
/// way. So a signed zero is not a representable `Float` term, and every IEEE rule whose result
/// depends on a zero's sign has no operand to act on.
///
/// This cell records what we ACTUALLY do at each such point, so that a change to the carrier turns
/// it red rather than passing silently. It is deliberately not a list of upstream's answers: those
/// are named in the message of each assertion, and closing the gap would cost the term algebra its
/// `Eq` — which is out of the 2026-07-29 ruling's scope.
#[tokio::test(flavor = "multi_thread")]
async fn signed_zero_is_the_carriers_divergence_and_it_is_pinned() {
    for (source, ours, upstream, note) in [
        ("float(-0.0, 64)", "0.0", "-0.0", "the literal itself collapses at parse time"),
        ("-float(0.0, 64)", "0.0", "-0.0", "`safe_neg` normalises `-0.0` to `+0.0`"),
        ("float(0.0, 64) - float(0.0, 64)", "0.0", "0.0", "IEEE agrees here: 0 - 0 is +0"),
        ("float(-0.0, 64) * float(1.0, 64)", "0.0", "-0.0", "the sign is already gone"),
        (
            "float(1.0, 64) / float(-0.0, 64)",
            "inf",
            "-inf",
            "IEEE's sign rule has no -0 to read",
        ),
        (
            "float(-1.0, 64) / float(-0.0, 64)",
            "-inf",
            "inf",
            "and likewise with the numerator negative",
        ),
    ] {
        let folded = fold(&parse(source)).unwrap_or_else(|err| panic!("{source:?}: {err}"));
        assert_eq!(
            folded, ours,
            "★ {source:?} answers {ours:?} here and {upstream:?} upstream ({note}). If this now \
             reads {upstream:?}, `CanonicalFloat64` stopped canonicalising signed zero — update \
             the module header's residual-divergence note, and check what it cost `Eq`/`Hash`.",
        );
    }
}

/// ★ `%` on floats needs NO change — MEASURED on both sides, and they already agree.
///
/// Rholang's `Mod` rule has no `CastFloat` arm at all (its only `safe_rem` call site is `i64`), so
/// two ground float operands fall to `binary_fallback` and answer the `error` term. Upstream's
/// `combine_mod` refuses `(GDouble, GDouble)` outright
/// (`rholang/src/rust/interpreter/reduce.rs:3424`). IEEE 754 §7.2 does make `x REM 0` and
/// `∞ REM y` invalid operations, but the operation is not *offered* on floats by either evaluator,
/// so there is no program whose acceptance differs — the floor is satisfied without a change.
///
/// ⚠ This is asserted rather than left as prose because "no float `%` arm" is a fact about the
/// grammar that a future carrier addition could quietly change, and if a float `%` arm ever appears
/// it must be built with `nan_is_a_value` from the start.
#[tokio::test(flavor = "multi_thread")]
async fn float_modulo_is_refused_by_both_evaluators_so_it_needs_no_ruling() {
    for source in [
        "float(5.0, 64) % float(2.0, 64)", // a TOTAL remainder — still refused, by both
        "float(1.0, 64) % float(0.0, 64)", // and the §7.2 invalid case
    ] {
        assert_eq!(
            fold(&parse(source)).unwrap_or_else(|err| panic!("{source:?}: {err}")),
            "error",
            "★ {source:?}: neither evaluator offers `%` on floats. If this ever computes, the arm \
             that was added must route through `nan_is_a_value` like the other four, and upstream's \
             `combine_mod` `GDouble` refusal has to be revisited at the same time.",
        );
    }
}

/// ★★ **Float comparison is a NUMERIC PREDICATE and follows IEEE-754.** RULED 2026-07-29, after
/// `b77e657c` / `ab885336` made `NaN` reachable and turned this from latent into observable.
///
/// | expression | before | now | upstream |
/// |---|---|---|---|
/// | `NaN == NaN` | `true`  | `false` | `false` |
/// | `NaN != NaN` | `false` | `true`  | `true`  |
/// | `NaN > 1.0`  | `true`  | `false` | `false` |
/// | `NaN >= NaN` | `true`  | `false` | `false` |
/// | `NaN < 1.0`  | `false` | `false` | `false` |
///
/// ## The two relations, and why the split is correct rather than an inconsistency
///
/// Rholang's `==`/`!=`/`<`/`<=`/`>`/`>=` on floats answer **"how do these two numbers compare?"**
/// Pattern matching, `Map` keys, `HashSet` membership and `SemanticHash` answer **"are these the
/// same term?"** Those are different questions, and a single relation cannot serve both: IEEE
/// equality is *deliberately irreflexive* on `NaN`, so it is **not an equivalence relation**, and a
/// term algebra cannot be built on one — `Eq`'s reflexivity contract would be violated and terms
/// would stop being usable as keys. So the arms compare raw `f64` (`.get()`) while
/// `CanonicalFloat64`'s `PartialEq`/`Ord` stay reflexive and total. **The carrier is unchanged.**
///
/// ⚠ **Upstream has the same split, and it was VERIFIED rather than assumed:**
/// * numeric — `combine_relop`'s `GDouble` arm (`reduce.rs:3146-3162`) returns `GBool(false)`
///   outright when either operand `is_nan()`, and `combine_eq` / `combine_neq` (`:3734`, `:3752`)
///   consult `par_contains_nan_double`. Both upstream tests are green:
///   `rholang_numeric_eval_spec::float_nan_comparisons_return_false` (all four ordered operators)
///   and `::float_nan_equality_follows_ieee754` (`==` false, `!=` true).
/// * structural — `RhoTypes.proto:269` declares `fixed64 g_double`, *"IEEE 754 f64 stored as raw
///   bits"*, so `GDouble(u64)`'s derived `PartialEq`/`Hash` compare BIT PATTERNS and two same-bit
///   `NaN`s are structurally equal.
///
/// ## The arm inventory
///
/// SIX arms, enumerated from the grammar rather than from a list of operators: `Eq`, `Ne`, `Gt`,
/// `Lt`, `GtEq`, `LtEq`. ★ Unlike the arithmetic arms these were a PLAIN fix, not an adapter
/// problem: `binop_to_safe_method` (`rust_code_rewrite.rs:206-215`) maps only `+ - * / %` and unary
/// `- !`, so `==`/`<`/`>` are `BinOp::Eq`/`Lt`/`Gt`, fall through, and are not safe-ified behind the
/// author's back. Only `CanonicalFloat64` has comparison arms: it is the sole float carrier in any
/// grammar (`rholang.rs:84` `![f64] as Float`; `calculator.rs:18` declares one too but has no
/// `CastFloat` arms at all). `QuietNaN` covers four carriers because `SafeArith` is a
/// general-purpose runtime library, not because four appear in a grammar.
#[tokio::test(flavor = "multi_thread")]
async fn float_comparison_is_a_numeric_predicate_and_follows_ieee754() {
    const NAN: &str = "(float(0.0, 64) / float(0.0, 64))";
    const POS_INF: &str = "(float(1.0, 64) / float(0.0, 64))";

    // ★ FLOOR 1: the NaN must exist, or every row below compares something else.
    assert_eq!(
        fold(&parse(NAN)).expect("the fold converges"),
        "NaN",
        "★ FLOOR: this cell is about comparisons ON a NaN; the NaN must be reachable first",
    );

    // ★ FLOOR 2: ordinary float comparisons must still be CORRECT, so no row below rests on a
    // comparator that has simply stopped working. All six operators, both verdicts each.
    for (source, expected) in [
        ("float(1.5, 64) < float(2.5, 64)", "true"),
        ("float(2.5, 64) < float(1.5, 64)", "false"),
        ("float(2.0, 64) == float(2.0, 64)", "true"),
        ("float(2.0, 64) == float(3.0, 64)", "false"),
        ("float(2.0, 64) != float(3.0, 64)", "true"),
        ("float(2.0, 64) != float(2.0, 64)", "false"),
        ("float(3.0, 64) >= float(3.0, 64)", "true"),
        ("float(2.0, 64) >= float(3.0, 64)", "false"),
        ("float(3.0, 64) <= float(3.0, 64)", "true"),
        ("float(4.0, 64) <= float(3.0, 64)", "false"),
        ("float(3.0, 64) > float(2.0, 64)", "true"),
        ("float(2.0, 64) > float(3.0, 64)", "false"),
    ] {
        assert_eq!(
            fold(&parse(source)).unwrap_or_else(|err| panic!("{source:?}: {err}")),
            expected,
            "★ FLOOR: {source:?} — an ordinary float comparison must still be correct",
        );
    }

    // ── IEEE 754 §5.11, per operator. `NaN` is UNORDERED: the only true predicate is `!=`. ──
    for (source, expected, arm) in [
        (format!("{NAN} == {NAN}"), "false", "Eq"),
        (format!("{NAN} == float(1.0, 64)"), "false", "Eq"),
        (format!("float(1.0, 64) == {NAN}"), "false", "Eq"),
        (format!("{NAN} != {NAN}"), "true", "Ne"),
        (format!("{NAN} != float(1.0, 64)"), "true", "Ne"),
        (format!("{NAN} > float(1.0, 64)"), "false", "Gt"),
        (format!("float(1.0, 64) > {NAN}"), "false", "Gt"),
        (format!("{NAN} < float(1.0, 64)"), "false", "Lt"),
        (format!("float(1.0, 64) < {NAN}"), "false", "Lt"),
        (format!("{NAN} >= {NAN}"), "false", "GtEq"),
        (format!("{NAN} >= float(1.0, 64)"), "false", "GtEq"),
        (format!("{NAN} <= {NAN}"), "false", "LtEq"),
        (format!("{NAN} <= float(1.0, 64)"), "false", "LtEq"),
        // CONTROL: an INFINITY is perfectly ordered, so it must NOT be swept up by the NaN rule.
        (format!("{POS_INF} > float(1e308, 64)"), "true", "Gt (control: +Inf is ordered)"),
        (format!("{POS_INF} == {POS_INF}"), "true", "Eq (control: +Inf equals itself)"),
        (format!("{POS_INF} >= {POS_INF}"), "true", "GtEq (control)"),
    ] {
        let folded = fold(&parse(&source)).unwrap_or_else(|err| panic!("{source:?}: {err}"));
        assert_eq!(
            folded, expected,
            "★★ {arm} arm — {source:?} must be {expected:?} (IEEE 754 §5.11). A `NaN` is UNORDERED: \
             every comparison but `!=` is false. If this reads the opposite, the arm is comparing \
             `CanonicalFloat64` values through the carrier's reflexive `PartialEq` / NaN-last `Ord` \
             instead of raw `f64` via `.get()`.",
        );
    }
}

/// ★★ **THE OTHER HALF OF THE SPLIT, AND IT IS INTENTIONAL — DO NOT "FIX" THIS.**
///
/// ⚠ A future reader will see that `NaN == NaN` folds to `false` and conclude that two `NaN` terms
/// must therefore be distinguishable to pattern matching, to a term-keyed container and to
/// `SemanticHash`, and will set out to make that so. **That would be a bug, not a fix.** This cell
/// exists to say so in the place where the change would be made, and to fail if it is.
///
/// STRUCTURAL IDENTITY answers a different question from a numeric predicate, and it requires an
/// EQUIVALENCE relation — reflexive, symmetric, transitive. IEEE equality is deliberately
/// irreflexive on `NaN` (§5.11), so it is not one. Adopting it for terms would cost, concretely:
///
/// * `BoundTerm::term_eq` is the relation the SPATIAL MATCHER uses, so an irreflexive `NaN` would
///   make a `NaN` term fail to match itself;
/// * `Eq`'s reflexivity is a `HashMap`/`HashSet` **soundness** requirement, not a style preference —
///   a key not equal to itself can be inserted and then never found again;
/// * `Proc::semantic_hash` would have to hash a value that compares unequal to itself, breaking
///   `a == b ⟹ hash(a) == hash(b)` in the direction that matters.
///
/// ⚠⚠ **And it is worse than that, MEASURED.** This cell was driven RED by patching
/// `CanonicalFloat64::PartialEq` to `self.0 == other.0` — i.e. by making the carrier follow IEEE —
/// and the result was not a failed assertion about map keys. It was
/// `generated Dovetail saturation for language Rholang stopped before convergence: IterationLimit`,
/// on the very first fold of `0.0 / 0.0`. **The rewrite engine stops terminating**: saturation
/// decides it has reached a fixpoint by comparing terms, and a term that is not equal to itself can
/// never be recognised as unchanged. So the reflexive carrier is not a convenience for containers,
/// it is a precondition for the fold converging at all.
///
/// So `CanonicalFloat64` canonicalises every `NaN` to one bit pattern and compares it equal to
/// itself (`runtime/src/canonical_float.rs:35-42`, `:94-135`) and the comparison ARMS reach past it
/// with `.get()`. ⚠ Upstream reaches the same arrangement from the other side, VERIFIED:
/// `RhoTypes.proto:269` declares `fixed64 g_double`, so `GDouble(u64)`'s derived `PartialEq`/`Hash`
/// compare bit patterns and two same-bit `NaN`s are structurally equal there too, while
/// `combine_relop` (`reduce.rs:3146-3162`) answers `false`.
#[tokio::test(flavor = "multi_thread")]
async fn two_nan_terms_stay_structurally_identical_and_that_is_deliberate() {
    use std::collections::HashMap;

    /// The hash a term-keyed container would use: `Proc::semantic_hash` run to a `u64`.
    fn sem(p: &Proc) -> u64 {
        use std::hash::Hasher;
        let mut h = std::collections::hash_map::DefaultHasher::new();
        p.semantic_hash(&mut h);
        h.finish()
    }

    let nan_a = fold_to_proc("float(0.0, 64) / float(0.0, 64)");
    let nan_b = fold_to_proc("float(0.0, 64) / float(0.0, 64)");
    // A second, INDEPENDENT route to a NaN, so this is about the value and not about two copies of
    // one expression: `Inf - Inf` is a different IEEE 754 §7.2 invalid operation from `0/0`.
    let nan_c =
        fold_to_proc("(float(1.0, 64) / float(0.0, 64)) - (float(1.0, 64) / float(0.0, 64))");
    let one = fold_to_proc("float(1.0, 64)");

    // ★ FLOOR: all three really are NaN terms, and the control really is not. Without this the
    // equalities below could hold because everything collapsed to the same non-NaN term.
    for (label, p) in [("nan_a", &nan_a), ("nan_b", &nan_b), ("nan_c", &nan_c)] {
        assert_eq!(p.to_string(), "NaN", "★ FLOOR: {label} must be a NaN term");
    }
    assert_eq!(one.to_string(), "1.0", "★ FLOOR: the control must not be a NaN");

    // ★ FLOOR: and the NUMERIC predicate really does disagree — otherwise this cell is not
    // documenting a split, it is documenting one relation twice.
    assert_eq!(
        fold(&parse("(float(0.0, 64) / float(0.0, 64)) == (float(0.0, 64) / float(0.0, 64))"))
            .expect("the fold converges"),
        "false",
        "★ FLOOR: `NaN == NaN` must be `false` for the split below to mean anything",
    );

    // ── STRUCTURAL, and INTENTIONAL. ──
    assert!(
        nan_a.term_eq(&nan_b),
        "★★ INTENTIONAL: two NaN terms are the SAME TERM. `==` on floats answers `false` because it \
         is a numeric predicate; `term_eq` is structural identity and is what the spatial matcher \
         uses, so it must stay an equivalence relation. Do not change it to agree with `==`.",
    );
    assert!(
        nan_a.term_eq(&nan_c),
        "★★ INTENTIONAL: and it does not depend on HOW the NaN arose — `0/0` and `Inf - Inf` are the \
         same term, because every NaN canonicalises to one bit pattern.",
    );
    assert!(
        !nan_a.term_eq(&one),
        "★ the CONTROL: a NaN term is not a `1.0` term — without this, `term_eq` returning `true` \
         for everything would satisfy the assertions above",
    );

    // `a == b ⟹ hash(a) == hash(b)`: the contract every hashed container over terms depends on.
    assert_eq!(
        sem(&nan_a),
        sem(&nan_c),
        "★★ INTENTIONAL: two `term_eq` NaN terms must hash the same under `semantic_hash`, or every \
         term-keyed container is unsound.",
    );
    assert_ne!(
        sem(&nan_a),
        sem(&one),
        "★ the CONTROL: distinct terms must not collapse to one hash, or the assertion above would \
         hold vacuously",
    );

    // The consequence, demonstrated: a value stored under one NaN term is retrievable by another.
    let mut store: HashMap<u64, &str> = HashMap::new();
    store.insert(sem(&nan_a), "stored under 0/0");
    assert_eq!(
        store.get(&sem(&nan_c)).copied(),
        Some("stored under 0/0"),
        "★★ INTENTIONAL: this is the reflexivity IEEE equality cannot provide and a term algebra \
         requires. If it ever returns `None`, someone made structural identity follow IEEE and \
         every NaN key in the system became unreachable.",
    );
}
