//! # RhoCalc ⟷ Rholang differential conformance suite (option C, Stage 0)
//!
//! ## Why this file exists
//!
//! RhoCalc ("MeTTaIL *is* Rholang 1.4") currently carries **two** implementations of the same
//! ground-data algebra:
//!
//! | # | Implementation | Where | Who runs it |
//! |---|---|---|---|
//! | ① | the `![{ … }]` **fold bodies** | `languages/src/rhocalc.rs` | MeTTaIL's Dovetail/e-graph (REPL, simulation) |
//! | ② | the **lowering** to `rhoapi::Par` | `rholang-runtime/src/rhocalc_ast.rs` | f1r3node's real reducer (`rholang/…/reduce.rs`) |
//!
//! Two implementations of one algebra can — and demonstrably **do** — diverge. This suite is the
//! *measurement instrument* for that divergence and the *acceptance gate* for the refactor that
//! removes it ("option C — different carriers, ONE evaluator": keep MeTTaIL's `Arc`-based,
//! hash-consed, moniker-bound AST as the carrier, but make the f1r3node consensus reducer the
//! sole *evaluator* of every operation Rholang already has).
//!
//! ## The invariant
//!
//! For a RhoCalc source expression `e`:
//!
//! ```text
//!                    ┌──────────────── ① fold ────────────────┐
//!                    │  Dovetail e-graph saturation over the  │
//!                    │  `![{…}]` native bodies                │──▶ RhoCalc surface display
//!   parse(e) ──▶ Proc┤                                        │            ║
//!    (ONE parse)     │                                        │            ║  must be EQUAL
//!                    │  lower_rhocalc_proc ▸ rhoapi::Par      │            ║
//!                    └──────────────── ② reduce ──────────────┘──▶ RuntimeObservationValue
//!                                                                          ║
//!                                                        render_as_rhocalc ╝
//! ```
//!
//! Both sides start from the **same** parsed `Proc`, so a parser/disambiguation difference can
//! never masquerade as a semantic one.
//!
//! ### The comparison is on VALUES, not carriers
//!
//! Carrier binding (making RhoCalc's categories literally be `rhoapi` types) is **blocked** and
//! deliberately not attempted: `models/src/rust/rhoapi_ext.rs:64-76` documents that `Ord` on `Par`
//! includes `locally_free` while the hand-written `PartialEq` ignores it — *"the wart is
//! load-bearing … do NOT 'fix' it"* — and MeTTaIL's collections and e-graph require `Ord` ⟷ `Eq`
//! agreement. So the two sides keep different carriers, and conformance is asserted on the
//! **observable value rendered in RhoCalc surface syntax**. [`render_as_rhocalc`] is that adapter;
//! it is part of the specification, not a convenience.
//!
//! ### The reducer is NORMATIVE
//!
//! Where the two disagree, `rholang/src/rust/interpreter/reduce.rs` (the consensus semantics) is
//! right and RhoCalc is wrong — "rhocalc IS rholang". Every divergence below is therefore recorded
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
//! | ID | Subject | RhoCalc fold ① | Rholang reducer ② | Closed by | Status |
//! |---|---|---|---|---|---|
//! | **A** | `Int` overflow | the **`error`** term (was: silently **`0`**) | wraps (`i64::MIN`) | C1 | open (fabrication fixed) |
//! | **A2** | `Int` division / remainder by zero | the **`error`** term (was: silently **`0`**) | `ReduceError("Division by zero")` | — | ★ CLOSED |
//! | **B** | `+` on a **runtime-bound** string | rests unreduced | `OperatorNotDefined { op: "+", other_type: "string" }` | C1 | open |
//! | **C** | `l.nth(i)` out of bounds, and `nth` on a plain (`BigInt`) index | the `error` term, all carriers (was: **process abort** / `error`) | recoverable `ReduceError` | C1 | open (fold half CLOSED) |
//! | **D** | `Fixed` arithmetic on **mismatched scales** | rescales | `OperatorExpectedError` | C1 | open |
//! | **E** | canonical **collection order** for `toByteArray` | protobuf byte order | `ScoredTerm` value order | C2 | ★ CLOSED |
//! | **F** | `.toByteArray()` | a hex `GString` — and unreachable from source | a real `GByteArray` | C2 | ★ CLOSED |
//! | **G** | `Pathmap` / zippers | own carriers + 20+ methods | `EPathmapBody`/`EZipperBody` exist, unused | C4 | open |
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
//! RhoCalc spells `or` at two levels, and `K` belongs to exactly one of them. The guard-level
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
//! `languages/tests/rhocalc_tests.rs::assert_reduces_to` — the helper behind most of that file's
//! RhoCalc semantics tests — reached its verdict through a disjunction ending in
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
//! guarantee itself is pinned by `rhocalc_tests.rs::comparator_integrity`.
//!
//! This suite still compares with `assert_eq!` on an explicitly written expected value and never
//! through a fuzzy helper.
//!
//! ### ⚠ Divergence A is NOT fixed here, and must not be
//!
//! f1r3node disagrees with **itself** about integer `+`:
//!
//! | Evaluator | `i64::MAX + 1` | Site |
//! |---|---|---|
//! | consensus reducer | **wraps** → `i64::MIN` | `rholang/src/rust/interpreter/reduce.rs:3106` `lhs.wrapping_add(rhs)` |
//! | guard evaluator | **errors** | `rho-pure-eval/src/eval.rs:144-146` `int_binop_checked("+", …, i64::checked_add)` |
//!
//! Reconciling those two is an **upstream f1r3node / consensus decision the USER has not made**,
//! and it is out of scope for MeTTaIL. What this suite *does* assert is the part that is
//! unambiguously MeTTaIL's problem: RhoCalc must not contribute a **third arithmetic answer**, and
//! must eventually inherit whichever f1r3node evaluator its lowering routes to — process position
//! ⟶ `reduce.rs`, guard position ⟶ `rho-pure-eval`. The 2026-07-25 fix removes the part that was
//! indefensible on its own terms — a *checked* operation FABRICATING `Default::default()` and
//! presenting it as the answer — leaving `error`, which is the absence of an answer rather than a
//! competing one. Inheriting the machine's answer is still C1's. The residual f1r3node-internal
//! inconsistency is recorded, not resolved.
//!
//! ## Operational note: fold panics ABORT the process here
//!
//! `catch_unwind` cannot contain a panic raised inside a Dovetail fold in this workspace: the
//! unwinder crosses Cranelift-compiled frames (`[profile.dev] codegen-backend = "cranelift"`,
//! workspace `Cargo.toml:79`) and dies with `fatal runtime error: failed to initiate panic,
//! error 5, aborting`. That is why every fold-side failure disposition in RhoCalc is a VALUE
//! (`Proc::Err`) and never a panic, and why
//! [`divergence_c_closed_nth_is_total_and_carrier_agnostic`] can assert an out-of-range `nth`
//! in-process: if the panic were back, the test binary would die instead of failing.

use std::sync::Arc;

use mettail_languages::rhocalc::{Name, Proc, RhoCalcLanguage, RhoCalcTerm, RhoCalcTermInner, Str};
use mettail_rholang_runtime::fold_contract::fold_definitions_for;
use mettail_rholang_runtime::rhocalc_ast::{clear_held_fold_sites, take_held_fold_sites};
use mettail_rholang_runtime::run::run_installed_program_with_call_definitions_and_read_runtime_values;
use mettail_rholang_runtime::{lower_rhocalc_proc, RhocalcAstLowerError, RHOCALC_BAG_ABI_TAG};
use mettail_runtime::{clear_var_cache, RuntimeObservationValue};
use models::rhoapi::Par;

// ════════════════════════════════════════════════════════════════════════════════════════════════
// Harness
// ════════════════════════════════════════════════════════════════════════════════════════════════

/// Dovetail saturation bounds — the same values the RhoCalc language test oracle uses
/// (`languages/tests/rhocalc_tests.rs::oracle`), so a fold that converges there converges here.
const DOVETAIL_ITERS: usize = 256;
const DOVETAIL_NODES: usize = 4_000_000;

/// Successor-edge bound for the COMM+fold fixpoint in [`fold_program`]. Generous: every
/// terminating program in this suite settles in fewer than ten steps.
const COMM_STEP_BOUND: usize = 64;

/// The ONE parse both sides share. `parse_via_wpda` is the disambiguated best-parse entry the
/// production AST-first lowering path uses (`rholang-runtime/tests/rho_rhocalc_ast.rs::parse_lower`).
fn parse(source: &str) -> Proc {
    clear_var_cache();
    Proc::parse_via_wpda(source)
        .unwrap_or_else(|err| panic!("rhocalc parse failed for {source:?}: {err}"))
}

/// ① the FOLD side: reduce `proc` to a Dovetail normal form and render it in RhoCalc surface
/// syntax.
///
/// Runs on a worker thread with a 32 MiB stack. The thread is not a panic *guard* (see the module
/// header — unwinding across Cranelift frames aborts); it exists so the deeply recursive generated
/// saturation code has the same headroom `RUST_MIN_STACK` gives the main test thread.
fn fold(proc: &Proc) -> Result<String, String> {
    let owned = proc.clone();
    std::thread::Builder::new()
        .name("rhocalc-fold".into())
        .stack_size(32 * 1024 * 1024)
        .spawn(move || {
            let term = RhoCalcTerm(RhoCalcTermInner::Proc(owned));
            RhoCalcLanguage::dovetail_normal_term(&term, DOVETAIL_ITERS, DOVETAIL_NODES)
                .map(|normal_form| normal_form.to_string())
                .map_err(|err| format!("dovetail: {err}"))
        })
        .expect("spawn the rhocalc fold worker")
        .join()
        .unwrap_or_else(|_| unreachable!("a fold panic aborts the process; it never unwinds here"))
}

/// ① the FOLD side for a whole PROGRAM: a bounded COMM+normalize fixpoint.
///
/// `dovetail_normal_term` alone folds native operators but does not fire a rendezvous, so a
/// program shaped `@("c")!(v) | for (@x <- @("c")) { … }` needs `Proc::try_comm_once` interleaved
/// with folding. This is exactly the `try_comm_anywhere` / `normalize_anywhere` loop the RhoCalc
/// language test oracle runs (`languages/tests/rhocalc_tests.rs:331` `run_fixpoint`), reduced to
/// the single-successor case this suite needs.
fn fold_program(proc: &Proc) -> Result<String, String> {
    let owned = proc.clone();
    std::thread::Builder::new()
        .name("rhocalc-fold-program".into())
        .stack_size(32 * 1024 * 1024)
        .spawn(move || {
            let mut current = owned;
            for _ in 0..COMM_STEP_BOUND {
                // Fold first: a send payload must be a value before the rendezvous delivers it.
                let term = RhoCalcTerm(RhoCalcTermInner::Proc(current.clone()));
                if let Ok(normal_form) =
                    RhoCalcLanguage::dovetail_normal_term(&term, DOVETAIL_ITERS, DOVETAIL_NODES)
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
        })
        .expect("spawn the rhocalc program-fold worker")
        .join()
        .unwrap_or_else(|_| unreachable!("a fold panic aborts the process; it never unwinds here"))
}

/// Unwrap a boxed `RhoCalcTerm` back to its `Proc` alternative (`None` for a non-`Proc` category
/// or an `Ambiguous` residue).
fn proc_of(term: &dyn mettail_runtime::Term) -> Option<Proc> {
    term.as_any()
        .downcast_ref::<RhoCalcTerm>()
        .and_then(|typed| match &typed.0 {
            RhoCalcTermInner::Proc(proc) => Some(proc.clone()),
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
    let par = lower_rhocalc_proc(program).map_err(|err| lower_error_message(&err))?;
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
/// fail-closed `UnsupportedProc` arm (`rholang-runtime/src/rhocalc_ast.rs::unsupported_construct_name`),
/// the debug form otherwise.
fn lower_error_message(err: &RhocalcAstLowerError) -> String {
    match err {
        RhocalcAstLowerError::UnsupportedProc(name) => format!("unsupported: {name}"),
        other => format!("lower: {other:?}"),
    }
}

// ════════════════════════════════════════════════════════════════════════════════════════════════
// The carrier adapter: `RuntimeObservationValue` ⟶ RhoCalc surface syntax
// ════════════════════════════════════════════════════════════════════════════════════════════════

/// Render a reducer observation in RhoCalc's own surface syntax, so it can be compared with a fold
/// normal form's `Display`.
///
/// This is the **specification of the carrier correspondence**, not a test convenience: it states,
/// value by value, which `rhoapi` ground datum RhoCalc considers to *be* which RhoCalc value.
/// Deliberately total-by-panic on the shapes this suite does not yet specify, so an unspecified
/// carrier can never be silently accepted as conformant.
fn render_as_rhocalc(value: &RuntimeObservationValue) -> String {
    match value {
        // The `Int` category ⟷ `ExprInstance::GInt`. ★ CORRECTED 2026-07-25 (divergence I):
        // this is the carrier of a PLAIN RhoCalc integer literal — `1`, `1i32`, `1i64`, `1u32`
        // — exactly as f1r3node's `normalize_ground` maps them, as well as of `int(a, w)`.
        RuntimeObservationValue::Int(literal) => literal.to_string(),
        // ⚠ The comment that stood here — "a plain RhoCalc integer literal is arbitrary-precision
        // (Rholang 1.4's default), so it rides as `GBigInt`" — was FACTUALLY WRONG, and stating
        // it in the conformance suite is part of why divergence I survived so long.
        // `normalize_ground` sends a bare numeral to `GInt`; only the `…n` spelling is `GBigInt`.
        // `GBigInt` is therefore rendered with the `n` tail its own grammar requires, which is
        // also what the fold's `Display` now emits (Stage C).
        RuntimeObservationValue::BigIntBytes(bytes) => {
            format!("{}n", num_bigint::BigInt::from_signed_bytes_be(bytes))
        },
        RuntimeObservationValue::Bool(literal) => literal.to_string(),
        // RhoCalc `Str` displays quoted; `{:?}` on `&str` is the same escaping RhoCalc's generated
        // `Display` uses for the shapes this suite covers (no embedded quotes/backslashes).
        RuntimeObservationValue::Text(text) => format!("{text:?}"),
        // `GDouble` carries the IEEE-754 bit pattern. `{:?}` keeps the trailing `.0` RhoCalc's
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
                    render_as_rhocalc(key),
                    render_as_rhocalc(mapped)
                ))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        RuntimeObservationValue::Tuple(items) => {
            format!("({})", render_all(items).join(", "))
        },
        other => panic!(
            "render_as_rhocalc: no RhoCalc surface form is specified for {other:?}; \
             add one deliberately rather than letting an unspecified carrier pass as conformant"
        ),
    }
}

fn render_all(values: &[RuntimeObservationValue]) -> Vec<String> {
    values.iter().map(render_as_rhocalc).collect()
}

/// Lowercase hex of a byte slice — the readable form of a `GByteArray` observation. (`languages`
/// carried a `hex` dependency solely for the retired wire fork's goldens; this suite does not
/// reintroduce one for six lines.)
fn hex_of(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

/// RhoCalc's `Fixed` surface form: the unscaled integer with a decimal point `scale` digits from
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

/// The suite's core assertion: `fold(e)`, `reduce(lower(e))`, and the human-written `expected`
/// RhoCalc surface form all agree.
///
/// `expected` is stated explicitly rather than only asserting `fold == reduce`, so a *mutual*
/// drift (both sides changing together) still fails.
async fn assert_conformant(source: &str, expected: &str) {
    let proc = parse(source);

    let folded = fold(&proc)
        .unwrap_or_else(|err| panic!("{source:?}: the RhoCalc fold did not converge: {err}"));
    assert_eq!(
        folded, expected,
        "{source:?}: the RhoCalc FOLD (languages/src/rhocalc.rs `![{{…}}]` bodies) \
         disagrees with the specified value"
    );

    let observed = reduce(&proc)
        .await
        .unwrap_or_else(|err| panic!("{source:?}: the Rholang REDUCE side failed: {err}"));
    let [value] = observed.as_slice() else {
        panic!("{source:?}: expected exactly one observation on @\"OUT\", got {observed:?}");
    };
    let rendered = render_as_rhocalc(value);
    assert_eq!(
        rendered, expected,
        "{source:?}: the Rholang REDUCER (f1r3node reduce.rs) disagrees with the specified value \
         (raw observation: {value:?})"
    );
}

// ════════════════════════════════════════════════════════════════════════════════════════════════
// PART 1 — the conformant surface (these MUST stay green through every refactor stage)
// ════════════════════════════════════════════════════════════════════════════════════════════════

/// Integer arithmetic on the two integer carriers. ★ CORRECTED 2026-07-25 (divergence I): a plain
/// RhoCalc integer literal is **`Int`**, riding `GInt` on the machine and `i64` in the fold, exactly
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
/// (`rholang-runtime/src/rhocalc_ast.rs:930-942`, `is_single_gstring_value`) that rewrites `+` to
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
/// this pins that `lower_rhocalc_proc` + the reducer agree with the fold's COMM+normalize
/// fixpoint on a *runtime-bound* integer operand. (The string twin of this shape is divergence
/// **B**.)
#[tokio::test(flavor = "multi_thread")]
async fn conformance_runtime_bound_integer_add_after_comm() {
    let source = r#"@("c")!(1) | for (@s <- @("c")) { @("OUT")!(s + 2) }"#;
    let proc = parse(source);
    let observed = reduce_program(&proc).await.expect("the program runs to rest");
    assert_eq!(
        observed.iter().map(render_as_rhocalc).collect::<Vec<_>>(),
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

/// **Divergence A (witness) — RhoCalc's fold FAILS CLOSED; it no longer fabricates a value.**
///
/// For `int(i64::MAX, 64) + int(1, 64)`:
///
/// | Implementation | Answer | Site |
/// |---|---|---|
/// | f1r3node consensus reducer | `i64::MIN` (wraps) | `rholang/src/rust/interpreter/reduce.rs:3106` `lhs.wrapping_add(rhs)` |
/// | f1r3node guard evaluator | an error | `rho-pure-eval/src/eval.rs:144-146` `int_binop_checked` |
/// | MeTTaIL RhoCalc fold | the **`error`** term | `languages/src/rhocalc.rs` `Add` body ▸ `SafeArith::safe_add` ▸ `None` ▸ `Proc::Err` |
///
/// **Amended 2026-07-25.** Until then the fold answered a silent **`0`**: its `Int` arm wrote
/// `(**a).clone() + (**b).clone()`, which reached a macro-emitted `impl std::ops::Add for Int`
/// whose failure path was `.unwrap_or_else(|| Int::NumLit(Default::default()))` — a *checked*
/// operation FABRICATING the category's `Default` on failure. That emitter fallback has been
/// deleted (`macros/src/gen/native/eval.rs`; no `std::ops::{Add,Sub,Mul,Div,Rem}` impl is emitted
/// for a category any more, so the fabrication is not expressible), and the fold arms now map
/// `SafeArith`'s `None` onto `Proc::Err` — the disposition the `UInt32`/`BigInt`/`BigRat`/`Fixed`
/// arms already used for ÷0.
///
/// A **wrong value** is therefore gone. A divergence remains, and it is the one this suite always
/// said it was: the fold does not INHERIT the evaluator its lowering routes to. That is still C1's
/// to close — see `divergence_a_target_int_overflow_inherits_the_f1r3node_evaluator`.
///
/// *Amend when C1 lands:* the fold body is gone, so both arms answer whatever `reduce.rs` answers.
#[tokio::test(flavor = "multi_thread")]
async fn divergence_a_witness_int_overflow_folds_to_the_error_term() {
    let source = "int(9223372036854775807, 64) + int(1, 64)";
    let proc = parse(source);

    assert_eq!(
        fold(&proc).expect("the fold converges"),
        "error",
        "A: RhoCalc's fold fails CLOSED on i64 overflow — never a fabricated value"
    );

    let observed = reduce(&proc).await.expect("the machine evaluates the sum");
    assert_eq!(
        observed.iter().map(render_as_rhocalc).collect::<Vec<_>>(),
        vec![i64::MIN.to_string()],
        "A: the consensus reducer wraps (reduce.rs:3106 wrapping_add)"
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
    let err = reduce(&proc).await.expect_err("the reducer refuses to divide by zero");
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
        // IEEE: `Inf - Inf` is NaN, which `SafeArith` declines.
        "float(1.0, 64) / float(0.0, 64)",
    ] {
        let folded = fold(&parse(source)).unwrap_or_else(|err| panic!("{source:?}: {err}"));
        assert_eq!(
            folded, "error",
            "{source:?} must fail CLOSED; a failed checked operation may never fabricate a value"
        );
    }
}

/// **Divergence A (target) — RhoCalc must INHERIT f1r3node's answer, never invent a third.**
///
/// This asserts only what is unambiguously MeTTaIL's to fix: the fold and the reducer must give
/// the *same* answer for the same expression in the same (process) position, whatever that answer
/// is. It deliberately does **not** decide the f1r3node-internal `reduce.rs` (`wrapping_add`) vs
/// `rho-pure-eval` (`checked_add`) question — that is an upstream consensus decision the USER has
/// not made, so it is asserted *relatively* (`fold == reduce`), never absolutely.
///
/// Closed by **C1** (deleting the arithmetic fold bodies makes the machine the only evaluator).
#[tokio::test(flavor = "multi_thread")]
#[ignore = "divergence A: RhoCalc's fold answers a silent 0 where f1r3node's reducer wraps; \
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
            render_as_rhocalc(value),
            "A: {source:?} — RhoCalc must inherit the f1r3node evaluator it routes to, \
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
/// `OperatorNotDefined`; concatenation is `++` (`EPlusPlus`, `reduce.rs:2760-2775`). RhoCalc's
/// surface uses `+`, so `rholang-runtime/src/rhocalc_ast.rs:930-942` bridges the gap with a shim
/// that emits `EPlusPlus` **iff** `is_single_gstring_value` holds of the *already-lowered* operand
/// `Par`s (`rhocalc_ast.rs:1107-1121`) — a purely static test.
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
        r#"@("OUT")!("hello world")"#
    );
    let observed = reduce_program(&ground).await.expect("the ground twin concatenates");
    assert_eq!(
        observed.iter().map(render_as_rhocalc).collect::<Vec<_>>(),
        vec![r#""hello world""#.to_string()]
    );
}

/// **Divergence B (target) — `+` on strings means ONE thing, decided by the value, not by what the
/// compiler happened to know.**
///
/// This asserts *position-independence* rather than a particular outcome, because the outcome is
/// USER decision **D-4** (§17.11.7): does RhoCalc conform *down* to Rholang — where `+` on strings
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
            ground_values.iter().map(render_as_rhocalc).collect::<Vec<_>>(),
            bound_values.iter().map(render_as_rhocalc).collect::<Vec<_>>(),
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

/// **Divergence C (parts 1 + 2) — ★ CLOSED 2026-07-25 on the FOLD side.**
///
/// Two of C's three symptoms were defects in `languages/src/rhocalc.rs`'s `LNth` body, and both
/// are fixed:
///
/// | symptom | before | now |
/// |---|---|---|
/// | out-of-range index | `v.get(n).cloned().expect("at: index out of bounds")` — a panic, which **aborts the process** here (unwinding across this workspace's Cranelift frames dies with `failed to initiate panic, error 5`) | the `error` term |
/// | index carrier | the arm matched only `(CastList, CastInt)`, so a PLAIN RhoCalc integer — which is `BigInt` — was rejected and `[1,2,3].nth(0)` answered `error` | `Int`, `BigInt` and `UInt32` indices all accepted |
///
/// This test is now a REGRESSION PIN, and it proves the panic is gone by construction: it calls
/// the out-of-range fold **in-process**. A panic would take the whole binary with it, so the test
/// cannot pass unless the fold returns.
///
/// The deleted machinery is worth naming: this used to be
/// `divergence_c_witness_out_of_bounds_nth_aborts_the_process`, which re-executed THIS test binary
/// as a child (armed by `MTL_DIVERGENCE_C_PROBE`) and asserted the child's death, because the abort
/// could not be observed any other way. With the panic gone there is nothing to survive.
///
/// The LOWERING half — `nth` never reaching the machine — was the remainder of C, and **C1 closed
/// it on 2026-07-26**: `nth` now routes to the reducer's own `nth`. See
/// [`divergence_c_target_nth_is_the_reducers_nth`], which is no longer `#[ignore]`d.
#[tokio::test(flavor = "multi_thread")]
async fn divergence_c_closed_nth_is_total_and_carrier_agnostic() {
    // Out of range: the `error` term, IN PROCESS (a panic here would abort the binary).
    for source in ["[1, 2, 3].nth(10)", "[1, 2, 3].nth(int(10, 64))", "[].nth(0)"] {
        assert_eq!(
            fold(&parse(source)).unwrap_or_else(|err| panic!("{source:?}: {err}")),
            "error",
            "C: {source:?} — an out-of-range `nth` is a value, never a panic"
        );
    }
    // Every integer carrier RhoCalc can write is accepted, and they agree.
    for source in ["[1, 2, 3].nth(0)", "[1, 2, 3].nth(int(0, 64))", "[1, 2, 3].nth(uint(0, 32))"] {
        assert_eq!(
            fold(&parse(source)).unwrap_or_else(|err| panic!("{source:?}: {err}")),
            "1",
            "C: {source:?} — `nth` does not care which integer carrier the index rode in on"
        );
    }
    // A NON-integer index is still refused, as a value.
    assert_eq!(fold(&parse(r#"[1, 2, 3].nth("0")"#)).expect("the fold converges"), "error");

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
/// (`reduce.rs:8464`). Out-of-bounds is now the reducer's recoverable error rather than a
/// MeTTaIL-side `error` term, which is the normative behaviour.
#[tokio::test(flavor = "multi_thread")]
async fn divergence_c_target_nth_is_the_reducers_nth() {
    // A plain (BigInt) index works, on both sides.
    assert_conformant("[1, 2, 3].nth(0)", "1").await;
    assert_conformant("[1, 2, 3].nth(2)", "3").await;
    // Out of bounds is a RECOVERABLE error, never a panic.
    let err = reduce(&parse("[1, 2, 3].nth(10)"))
        .await
        .expect_err("out-of-bounds `nth` must be a recoverable reduction error");
    assert!(
        err.contains("index out of bound"),
        "C: expected Rholang's `index out of bound` error, got {err:?}"
    );
}

// ── D — `Fixed` scale mismatch ───────────────────────────────────────────────────────────────────

/// **Divergence D (witness) — the fold rescales where the reducer refuses.**
///
/// `rholang/src/rust/interpreter/reduce.rs:3193-3200` requires `fp1.scale == fp2.scale` and
/// otherwise raises `OperatorExpectedError { expected: "FixedPoint(pN)" }`. RhoCalc's `Add` body
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
    let err = reduce(&proc).await.expect_err("the reducer rejects mismatched scales");
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
                render_as_rhocalc(value),
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
/// `EMethod("toByteArray")` (`rholang-runtime/src/rhocalc_ast.rs::lower_method`) and the reducer
/// evaluates it (`reduce.rs:4137-4160` — `eval_expr` + `substitute`, then `p.encode_to_vec()`),
/// returning a real `GByteArray`.
///
/// ### What was retired, and why the goldens changed
///
/// `languages/src/rhocalc/wire.rs` + `languages/proto/rhocalc_wire.proto` + `languages/build.rs`
/// were a hand-maintained **fork** of f1r3node's `rhoapi` schema (7 of its 62 messages), compiled
/// by `protoc` into a *second* `rhoapi::Par` type in the same workspace. Three independent defects
/// made it unsalvageable rather than merely redundant:
///
/// | # | Defect | Consequence |
/// |---|---|---|
/// | 1 | the fork's `.proto` had **no `g_big_int` field**, and `proc_to_par` matched only `Proc::CastInt(Int::NumLit(_))` | a plain RhoCalc integer literal is arbitrary-precision (`CastBigInt`), so `.toByteArray()` folded to `error` for every collection the grammar produces |
/// | 2 | it sorted set/map members by raw **protobuf byte order** (`wire.rs:19-25`, `sort_by_key(encode_to_vec)`) | disagrees with Rholang's **`ScoredTerm` value order** (`models/src/rust/sorted_par_hash_set.rs:22`) on negative integers — divergence **E** |
/// | 3 | it returned a **hex `GString`**, not a `GByteArray` (`wire.rs:136-139`) | the wrong Rholang carrier — divergence **F** |
///
/// ### ★ RE-MEASURED 2026-07-25 after divergence I closed
///
/// The C2 goldens were re-baselined onto `GBigInt` leaves (`9a 02 01 0N`) because a plain RhoCalc
/// numeral was then a `CastBigInt`. **It should never have been**: `normalize_ground` maps a bare
/// numeral to `GInt`, and divergence I fixed the grammar accordingly. So these goldens are measured
/// again, deliberately — a carrier change moves the wire bytes, and rubber-stamping them would have
/// hidden exactly the thing this suite exists to catch.
///
/// The new bytes for `[1,2,3]`, `2a15a201120a042a0210020a042a0210040a042a021006`, are **byte-
/// identical to the goldens the RETIRED FORK produced** (`GInt` elements, `sint64` zigzag
/// `02 04 06` = 1, 2, 3). That is a receipt, not a coincidence: defect #1 in the table above was
/// that the fork's `.proto` had no `g_big_int` field — the fork was encoding what Rholang actually
/// means, and only *looked* wrong because RhoCalc's literals were landing in the wrong carrier.
/// The `GBigInt` encoding is now reached by exactly the spelling that asks for it, `[1n, 2n, 3n]`
/// (pinned below).
///
/// (The five golden-hex tests that pinned the fork lived in
/// `languages/tests/rhocalc_tests.rs::native_ops::collection_wire`. They were retired rather than
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
        let observed = reduce(&parse(source)).await.unwrap_or_else(|err| {
            panic!("{source:?}: the machine must own toByteArray: {err}")
        });
        let [RuntimeObservationValue::Bytes(bytes)] = observed.as_slice() else {
            panic!("{source:?}: `toByteArray` must return a GByteArray, got {observed:?}");
        };
        assert_eq!(hex_of(bytes), expected, "{source:?}");
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
/// (`rholang-runtime/src/rhocalc_ast.rs`) represents it as an `EList` tagged with
/// `RHOCALC_BAG_ABI_TAG` (`mettail.rhocalc.bag.v1`, visible in the bytes below) carrying
/// `(element, count)` pairs. The retired fork instead **expanded the multiset** into a bare
/// `EList` of repeated elements, discarding both the tag and the count structure — so its bytes
/// decoded back to a *list*, not a bag. Routing through `EMethod` means the bytes are the encoding
/// of the term RhoCalc actually lowers.
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
        encoded.contains(&hex_of(RHOCALC_BAG_ABI_TAG.as_bytes())),
        "the bag ABI tag must ride the encoding, got {encoded}"
    );
    assert_eq!(
        encoded,
        // ★ RE-MEASURED 2026-07-25 (divergence I): the ELEMENT leaves are now `GInt` (`2a 02 10`)
        // rather than `GBigInt` (`9a 02`); the `(element, count)` pair structure and the ABI tag
        // are unchanged. The counts were always `GInt`, so each pair is now homogeneous.
        "2a50a2014d0a1e3a1c0a1a0a180a166d65747461696c2e72686f63616c632e6261672e76310a2b2a29\
         a201260a112a0fa2010c0a042a0210020a042a0210020a112a0fa2010c0a042a0210040a042a021004"
    );
}

// ── G — Pathmap and zipper carriers ──────────────────────────────────────────────────────────────

/// **Divergence G (witness) — `Pathmap` lowers to `EMap`, so the trie carrier is discarded.**
///
/// `rhoapi` already declares `e_pathmap_body = 32` and `e_zipper_body = 33`, and
/// `rholang/src/rust/interpreter/reduce.rs` already implements
/// `readZipper/writeZipper/descendTo/getLeaf/getSubtrie/graft/joinInto/ascend/childCount/…`. But
/// `rholang-runtime/src/rhocalc_ast.rs::lower_pathmap` (line 2317) lowers `Pathmap` to **`EMap`**,
/// discarding the trie structure, so the ~8 pathmap and ~15 zipper methods implemented MeTTaIL-side
/// (`languages/src/rhocalc/{pathmap,zipper}.rs`) never reach their native counterpart.
///
/// ★ AMENDED by C1 (2026-07-26). The second half of this witness used to assert that pathmap and
/// zipper methods "never reach the machine at all", i.e. that they were rejected at the LOWERING:
///
///     for (source, expected_error) in [
///         ("{|1:2|}.get(1)", "unsupported: m.get(k) map method"),
///         ("{|1:2|}.union({|3:4|})", "unsupported: m.union(n) map method"),
///         ("{|1:2|}.readZipper()", "unsupported: p.readZipper() zipper method"),
///     ] { … }
///
/// That is no longer the shape of G. C1 routes all three, so they now reach the reducer and are
/// refused at the CARRIER instead — which is a strictly better statement of the same divergence,
/// because the carrier is the thing C4 fixes. The two live halves below are the amended assertions;
/// the full method-by-method picture is
/// [`c1_pathmap_methods_answer_through_the_emap_encoding`] and
/// [`c1b_pathmap_zipper_family_is_c4_blocked_at_the_carrier`].
///
/// *Delete when C4 lands.*
#[tokio::test(flavor = "multi_thread")]
async fn divergence_g_witness_pathmap_lowers_to_emap_and_zippers_are_unsupported() {
    // The pathmap literal round-trips through the fold as a pathmap …
    assert_eq!(fold(&parse("{|1:2|}")).expect("the fold converges"), "{|1:2|}");
    // … but the machine only ever sees a Map.
    let observed = reduce(&parse("{|1:2|}")).await.expect("the literal lowers");
    assert!(
        matches!(observed.as_slice(), [RuntimeObservationValue::Map(_)]),
        "G: the trie carrier is discarded — the machine observes an EMap, got {observed:?}"
    );

    // ① A method Rholang defines on a Map now ANSWERS, through the encoding, because the encoding
    //    happens to be key-faithful. The value is right; it is the carrier that was lost.
    let observed = reduce(&parse("{|1:2|}.get(1)")).await.expect("get routes and answers");
    assert_eq!(observed.iter().map(render_as_rhocalc).collect::<Vec<_>>(), vec!["2".to_string()]);

    // ② A method that needs the TRIE cannot be rescued by a key-faithful encoding: it reaches the
    //    reducer and is refused at the carrier. This is G, stated where it actually bites.
    assert_eq!(
        reduce(&parse("{|1:2|}.readZipper()")).await.expect_err("no EPathmapBody exists yet"),
        r#"reduce: inj: MethodNotDefined { method: "readZipper", other_type: "map" }"#,
        "G: a zipper cannot be built over an EMap — this is exactly what C4 closes"
    );
}

/// **Divergence G (target) — `Pathmap` is `EPathmapBody` and zippers are `EZipperBody`.**
///
/// Closed by **C4**. This is the divergence with the most strategic weight: the in-flight EPathMap
/// wire-model campaign needs RhoCalc pathmaps to land on the *real* `EPathMap` carrier, not on an
/// `EMap` that has already thrown the trie structure away.
#[tokio::test(flavor = "multi_thread")]
#[ignore = "divergence G: Pathmap lowers to EMap and zippers are UnsupportedProc despite \
            e_pathmap_body=32 / e_zipper_body=33 existing; closed by C4"]
async fn divergence_g_target_pathmap_and_zippers_use_their_native_carriers() {
    let observed = reduce(&parse("{|1:2|}")).await.expect("the pathmap literal lowers");
    assert!(
        !matches!(observed.as_slice(), [RuntimeObservationValue::Map(_)]),
        "G: a Pathmap must not observe as an EMap — the trie carrier must survive lowering"
    );
    reduce(&parse("{|1:2|}.get(1)"))
        .await
        .expect("G: pathmap methods must reach the reducer's own pathmap method table");
    reduce(&parse("{|1:2|}.readZipper()"))
        .await
        .expect("G: zipper construction must reach EZipperBody");
}

// ── H — boolean equality (discovered by this suite) ──────────────────────────────────────────────

/// **Divergence H — ★ CLOSED 2026-07-25.**
///
/// H was discovered by this suite: `languages/src/rhocalc.rs`'s `Eq`/`Ne` fold bodies had arms for
/// every ground type EXCEPT `Bool`, so `true == true` fell through to the collection-equality
/// fallback and answered `Proc::Err`, while the machine answered `true`.
///
/// Rholang is normative and Rholang's `==` is STRUCTURAL equality on the whole `Par`
/// (`reduce.rs::combine_eq`, `sv1 == sv2` after substitution — not `relopb`, which serves only
/// `<`/`<=`/`>`/`>=`), so two `GBool`s compare by value. RhoCalc now has the matching `Bool` arm
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

/// **Divergence I — ★ CLOSED 2026-07-25 in the GRAMMAR (`languages/src/rhocalc.rs`).**
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
/// The MeTTaIL-side pins are `languages/tests/rhocalc_tests.rs::numeral_carrier_is_context_
/// independent`.
#[tokio::test(flavor = "multi_thread")]
async fn divergence_i_closed_numeral_carrier_is_syntax_independent() {
    assert_conformant("int(1, 64) + 2", "3").await;
    // (`5u32 bitand 3u32` is pinned on the MeTTaIL side only — `bitand` is a MeTTaIL-only
    // operation with no Rholang `Expr`, so it is C3 residue and cannot be asserted CONFORMANT.
    // Its carrier claim lives in `languages/tests/rhocalc_tests.rs::
    // numeral_carrier_is_context_independent::u32_suffix_is_an_i64_literal`.)
    assert_conformant("5u32 + 3u32", "8").await;
    // The parenthesis witness itself: one pair of parentheses used to change the carrier.
    assert_conformant("*(@1) + 2", "3").await;
    assert_conformant("*(@(1)) + 2", "3").await;
    // The computed-vs-literal witness. `.length()` is C1 residue (no Rholang list method — see
    // `c1_inventory_witness_collection_methods_are_not_lowered`), so only the FOLD side can be
    // asserted; what matters here is that a COMPUTED integer and a LITERAL one are now the same
    // carrier. Before divergence I closed, every computed integer was an `Int` and every literal
    // was a `BigInt`, so this answered `error`.
    assert_eq!(
        fold(&parse("[1, 2, 3].length() == 3")).expect("the fold converges"),
        "true",
        "a computed integer and a literal one share one carrier"
    );
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
/// RhoCalc canonicalizes every send payload to a LIST (`x!(p)` ≡ `x!([p])`, `x!()` ≡ `x!([])` —
/// pinned by `languages/tests/rhocalc_tests.rs::parsing::{send_unary_is_list_sugar,
/// send_empty_is_list_sugar}`), and a whole-message binder receives that payload. So the 0-arity
/// send `x!()` satisfies the 1-arity receive `for(@y <- x)` and binds `y = []`.
///
/// Rholang's COMM is ARITY-CHECKED: `x!()` produces a `Send` with an empty `data` vector, and a
/// `Receive` whose single `ReceiveBind` has one pattern never matches it, so the program rests.
/// (RhoCalc agrees for multi-binder rows — `x!(1,2) | for(a,b,c <- x){…}` blocks — so the
/// divergence is specific to the whole-message binder against the EMPTY payload.)
///
/// Discovered while burning down `languages/tests/rhocalc_tests.rs`, where
/// `send_empty_payload_quoted_bind_emits_empty_proc` had an expectation that contradicted both its
/// own name and the sugar pins, and only "passed" because `assert_reduces_to` was vacuous.
#[tokio::test(flavor = "multi_thread")]
async fn divergence_j_witness_empty_send_satisfies_an_arity_one_receive() {
    assert_eq!(
        fold_program(&parse("for(@y <- x){y} | x!()")).expect("the fold fixpoint settles"),
        "{[]}",
        "J: the empty send's payload IS `[]`, and the whole-message binder receives it"
    );
    // The multi-binder row is arity-checked, so the divergence is not "RhoCalc ignores arity".
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
    assert!(
        folded.contains("for("),
        "J: the receive must still be waiting, got {folded:?}"
    );
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
/// (`rholang-runtime/src/rhocalc_ast.rs::unsupported_construct_name`).
///
/// *Amend when C3 lands:* each of these becomes a system-process `Definition` invocation, so the
/// machine answers instead of rejecting — but the answer still comes from the SAME single Rust
/// implementation the fold used.
#[tokio::test(flavor = "multi_thread")]
async fn c3_residue_mettail_only_operations_fail_closed_and_named() {
    for (source, fold_answer, machine_error) in [
        ("fraction(1, 2)", "1/2", "unsupported: fraction(a, b) rational constructor"),
        // `reduce.rs::method_table` provides `keys` but NOT `values` — a Map's values are
        // reachable in Rholang only via `toList`/`get`. So `.values()` is a RhoCalc extension
        // with no Rholang counterpart, and it stays MeTTaIL-only under C3.
        (
            "{1 : 10}.values()",
            "[10]",
            "unsupported: m.values() map method (no Rholang analog; C3 residue)",
        ),
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
/// `EList[GPrivate(RHOCALC_BAG_ABI_TAG), EList[pairs]]` — is refused by name and type.
///
/// The hazard the note was reaching for is real, but it lives on the two routed methods that DO
/// accept `EListBody` (`length`, `nth`), and those are gated at the lowering; see
/// [`c1_bag_length_and_nth_are_gated_at_lowering`] and the residue witness
/// [`c1_bag_length_residue_when_the_carrier_is_only_known_at_runtime`].
///
/// Every row here is a method whose fold body accepts a `Bag`. The machine must fail CLOSED —
/// never answer about the encoding.
#[tokio::test(flavor = "multi_thread")]
async fn c1_bag_encoding_is_rejected_by_every_routed_method() {
    for (source, fold_answer, machine_error) in [
        (
            "#{1 | 2 | 2}#.size()",
            "3",
            r#"reduce: inj: MethodNotDefined { method: "size", other_type: "list" }"#,
        ),
        (
            "#{1 | 2 | 2}#.union(#{3}#)",
            "#{1| 2| 2| 3}#",
            r#"reduce: inj: MethodNotDefined { method: "union", other_type: "list" }"#,
        ),
        (
            "#{1 | 2 | 2}#.diff(#{2}#)",
            "#{1| 2}#",
            r#"reduce: inj: MethodNotDefined { method: "diff", other_type: "list" }"#,
        ),
    ] {
        let proc = parse(source);
        assert_eq!(
            fold(&proc).expect("the fold converges"),
            fold_answer,
            "C1: {source:?} — the MeTTaIL-side multiset answer"
        );
        assert_eq!(
            reduce(&proc).await.expect_err("the bag encoding must be refused"),
            machine_error,
            "C1: {source:?} — the machine must REFUSE the bag encoding, not measure it"
        );
    }
}

/// **`length`, `nth` and `concat` are gated at the lowering, because the reducer WOULD answer.**
///
/// These are exactly the routed operations whose interpreter implementation accepts `EListBody`,
/// and therefore exactly the ones that could measure the 2-element bag ABI encoding and return
/// something plausible instead of failing:
///
/// | operation | interpreter | accepts `EList`? | ungated answer for a bag |
/// |---|---|---|---|
/// | `length` | `length_method` (7893) | **yes** | `2` — tag + pairs — not the cardinality `3` |
/// | `nth` | `nth_method` (4078) | **yes** | the ABI tag, or the pairs list |
/// | `concat` | `combine_plus_plus` | **yes** | a 4-element list carrying TWO ABI tags |
///
/// Every other routed method accepts only `EMapBody`/`ESetBody`/`EPathmapBody` and so refuses the
/// encoding by itself — measured in [`c1_bag_encoding_is_rejected_by_every_routed_method`]. The
/// gate ([`receiver_is_literal_bag`] in `rhocalc_ast.rs`) covers the case decidable at lowering
/// time; `concat` checks BOTH operands, since either position can supply the bag.
#[tokio::test(flavor = "multi_thread")]
async fn c1_bag_length_and_nth_are_gated_at_lowering() {
    for (source, expected_error) in [
        ("#{1 | 2 | 2}#.length()", "bag cardinality"),
        ("#{1 | 2 | 2}#.nth(0)", "bag indexing"),
        ("#{1 | 2 | 2}#.concat(#{3}#)", "bag concatenation"),
        // the bag in the RIGHT operand only — the gate is not left-biased
        ("[1, 2].concat(#{3}#)", "bag concatenation"),
    ] {
        let proc = parse(source);
        let error = reduce(&proc).await.expect_err("the bag gate must fire");
        assert!(
            error.starts_with("unsupported: ") && error.contains(expected_error),
            "C1: {source:?} — expected a fail-closed LOWERING error naming the bag, got {error:?}"
        );
        assert!(
            error.contains("C3 residue"),
            "C1: {source:?} — the error must name the stage that closes it, got {error:?}"
        );
    }
}

/// **⚠ THE MEASURED RESIDUE: the bag gate cannot see a carrier that is only known at run time.**
///
/// `[#{1|2|2}#].nth(0)` has receiver type `Bag`, but its *syntax* is `LNth`, not `CastBag`, so no
/// shape check at the lowering can refuse it — and neither can one refuse a COMM-bound variable.
/// The reducer then measures the bag ABI encoding: **2**, where the fold answers the multiset
/// cardinality **3**.
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
    assert_eq!(
        fold(&proc).expect("the fold converges"),
        "3",
        "the fold measures the MULTISET"
    );
    let observed = reduce(&proc).await.expect("the machine reduces");
    assert_eq!(
        observed.iter().map(render_as_rhocalc).collect::<Vec<_>>(),
        vec!["2".to_string()],
        "C1 residue: the machine measures the 2-element bag ABI ENCODING. If this is now 3, C3 \
         landed — promote this witness to a conformance row"
    );
}

/// **C1b — the Pathmap/Zipper family is routed, and blocked at the CARRIER by C4.**
///
/// Every one of these methods requires an `EPathmapBody` or `EZipperBody` receiver
/// (`reduce.rs:4926` `readZipper`, `5322` `getSubtrie`, …), and RhoCalc's `Pathmap` still lowers
/// to a plain `EMap` — divergence **G**. So the routing is correct and inert: the machine names
/// the carrier that is wrong, which is exactly what C4 fixes.
///
/// ★ This is the answer to "is C4 still a blocker for C1?": **yes, but only for this family.** The
/// ordinary list/string/set/map surface routes and agrees today, with no dependency on C4 at all.
#[tokio::test(flavor = "multi_thread")]
async fn c1b_pathmap_zipper_family_is_c4_blocked_at_the_carrier() {
    for (source, method) in [
        ("{| 1 : 10, 2 : 20 |}.readZipper().leafCount()", "readZipper"),
        ("{| 1 : 10, 2 : 20 |}.readZipper().toNextLeaf().getPath()", "readZipper"),
        ("{| 1 : 10, 2 : 20 |}.readZipper().childCount()", "readZipper"),
        ("{| 1 : 10 |}.getSubtrie()", "getSubtrie"),
    ] {
        let proc = parse(source);
        let error = reduce(&proc).await.expect_err("the EMap carrier must be refused");
        assert_eq!(
            error,
            format!(r#"reduce: inj: MethodNotDefined {{ method: "{method}", other_type: "map" }}"#),
            "C1b: {source:?} — the method must reach the reducer and be refused at the CARRIER \
             (divergence G / C4), not rejected at the lowering"
        );
    }
}

/// **Divergence G, sharpened by C1: a routed Pathmap method answers through the `EMap` encoding.**
///
/// Because `lower_pathmap` emits a plain `EMap`, a routed method sees a Map. That splits three
/// ways, and all three are measured here rather than assumed:
///
/// 1. **key-faithful and AGREEING** — `get`/`contains` read the same key/value relation the fold
///    reads, so both sides answer identically;
/// 2. **the machine is MORE DEFINED than the fold** — `size`/`keys`/`delete` answer on the machine
///    where RhoCalc's fold bodies have no `Pathmap` arm and reduce to `error`. Under "the reducer
///    is normative" the machine is right and the fold is incomplete;
/// 3. **⚠ the CARRIER of the result differs** — `set`/`union` return a `Pathmap` from the fold and
///    a `Map` from the machine. The VALUE is the same relation; the type is not, and a `Pathmap`
///    method applied to that result would then fail. This is the concrete cost of divergence G and
///    it closes with C4.
#[tokio::test(flavor = "multi_thread")]
async fn c1_pathmap_methods_answer_through_the_emap_encoding() {
    // ① key-faithful: the two sides agree outright.
    assert_conformant("{| 1 : 10, 2 : 20 |}.get(1)", "10").await;
    assert_conformant("{| 1 : 10, 2 : 20 |}.contains(1)", "true").await;

    // ② the machine is more defined than the fold.
    for (source, machine_answer) in [
        ("{| 1 : 10, 2 : 20 |}.size()", "2"),
        ("{| 1 : 10, 2 : 20 |}.keys()", "Set(1, 2)"),
        ("{| 1 : 10, 2 : 20 |}.delete(1)", "{2:20}"),
    ] {
        let proc = parse(source);
        assert_eq!(
            fold(&proc).expect("the fold converges"),
            "error",
            "G: {source:?} — RhoCalc's fold body has no Pathmap arm"
        );
        let observed = reduce(&proc).await.expect("the machine reduces");
        assert_eq!(
            observed.iter().map(render_as_rhocalc).collect::<Vec<_>>(),
            vec![machine_answer.to_string()],
            "G: {source:?} — the machine answers through the EMap encoding"
        );
    }

    // ③ ⚠ same value, different CARRIER: `{|…|}` from the fold, `{…}` from the machine.
    for (source, fold_answer, machine_answer) in [
        (
            "{| 1 : 10, 2 : 20 |}.set(3, 30)",
            "{|1:10, 2:20, 3:30|}",
            "{1:10, 2:20, 3:30}",
        ),
        (
            "{| 1 : 10, 2 : 20 |}.union({| 3 : 30 |})",
            "{|1:10, 2:20, 3:30|}",
            "{1:10, 2:20, 3:30}",
        ),
    ] {
        let proc = parse(source);
        assert_eq!(fold(&proc).expect("the fold converges"), fold_answer);
        let observed = reduce(&proc).await.expect("the machine reduces");
        assert_eq!(
            observed.iter().map(render_as_rhocalc).collect::<Vec<_>>(),
            vec![machine_answer.to_string()],
            "G: {source:?} — the machine cannot return a Pathmap it has no carrier for"
        );
    }
}

/// **`length` on a Map/Set: RhoCalc's fold body is MORE PERMISSIVE than Rholang.**
///
/// `fold_proc_length` (`languages/src/rhocalc/runtime.rs:217`) answers for `CastMap` and
/// `CastSet`; Rholang's `length` (`reduce.rs:7893`) accepts only `EList`/`GString`/`GByteArray`
/// and spells map/set cardinality `size`. Since the reducer is normative, the fold is the side
/// that is wrong, and routing makes the machine fail closed rather than inventing an answer.
#[tokio::test(flavor = "multi_thread")]
async fn c1_length_on_a_map_is_fold_only() {
    for (source, fold_answer, other_type) in
        [("{1 : 10}.length()", "1", "map"), ("Set(1, 2).length()", "2", "set")]
    {
        let proc = parse(source);
        assert_eq!(fold(&proc).expect("the fold converges"), fold_answer);
        assert_eq!(
            reduce(&proc).await.expect_err("Rholang spells this `size`"),
            format!(
                r#"reduce: inj: MethodNotDefined {{ method: "length", other_type: "{other_type}" }}"#
            ),
            "C1: {source:?} — Rholang has no `length` for this carrier"
        );
    }
}

/// **The C1 residue: methods with NO key in `reduce.rs::method_table`, fail-closed and NAMED.**
///
/// There is nothing to route these to — routing would have to *invent* an implementation, which is
/// the one thing option C exists to prevent. `values`/`count`/`remove`/`subtract` have no key at
/// all; `restrict`/`meet`/`getSubtrieAt` have plausible but UNVERIFIED candidates (`restriction`,
/// `intersection`, `getSubtrie`+`atPath`) which cannot be exercised even once while `Pathmap`
/// lowers to `EMap`, so shipping the rename would be an untested semantic claim. Each error names
/// the construct and the stage that closes it.
#[tokio::test(flavor = "multi_thread")]
async fn c1_residue_without_an_interpreter_counterpart_fails_closed_and_named() {
    for (source, expected_error) in [
        ("{1 : 10}.values()", "unsupported: m.values() map method (no Rholang analog; C3 residue)"),
        (
            "#{1 | 2 | 2}#.count(2)",
            "unsupported: b.count(e) bag method (no Rholang analog; C3 residue)",
        ),
        (
            "#{1 | 2 | 2}#.remove(2)",
            "unsupported: b.remove(e) bag method (no Rholang analog; C3 residue)",
        ),
        (
            "{| 1 : 10 |}.subtract({| 1 : 10 |})",
            "unsupported: p.subtract(q) pathmap method (no Rholang analog; C3 residue)",
        ),
    ] {
        let proc = parse(source);
        assert_eq!(
            reduce(&proc).await.expect_err("no counterpart exists"),
            expected_error,
            "C1: {source:?} — must fail closed, NAMING the construct"
        );
    }
    // The three whose candidate mapping is unverifiable until C4 makes it measurable.
    for (source, candidate) in [
        ("{| 1 : 10 |}.restrict({| 1 : 10 |})", "restriction"),
        ("{| 1 : 10 |}.meet({| 1 : 10 |})", "intersection"),
        ("{| 1 : 10 |}.getSubtrieAt(1)", "no single-method analog"),
    ] {
        let proc = parse(source);
        let error = reduce(&proc).await.expect_err("no verified counterpart exists");
        assert!(
            error.contains(candidate) && error.contains("until C4"),
            "C1: {source:?} — the error must name the candidate and the stage, got {error:?}"
        );
    }
}

/// **★ C1, LANDED — every routed collection method is evaluated by the reducer's own method
/// table, and agrees with the fold body it now shares the surface with.**
///
/// Each row is a DIFFERENTIAL: the same parsed `Proc` is folded by MeTTaIL's Dovetail saturation
/// and lowered to the real reducer, and the two observable values must match. Both paths still
/// exist — C1 routed the LOWERING; it did not delete the `![{…}]` fold bodies (that is C1's
/// sequel, and it needs C3/C4 first, since some fold bodies are the only implementation of an
/// operation Rholang cannot perform). So this suite is exactly the instrument that proves the two
/// implementations agree wherever both are defined.
///
/// `assert_conformant` compares the RhoCalc-rendered values, so a row passing here also pins the
/// **canonical order** question: a set/map result flowing back from the reducer has been through
/// `ScoredTerm` sorting (`models/src/rust/sorted_par_hash_set.rs`), and `Set(1, 2).union(Set(3))`
/// rendering as `Set(1, 2, 3)` on both sides is the evidence that the two orders coincide for
/// these values — see `c1_routed_results_carry_the_reducer_canonical_order` for the case built to
/// separate them.
#[tokio::test(flavor = "multi_thread")]
async fn c1_target_collection_methods_route_to_the_reducer() {
    // list / string — `length`, `nth`, and `concat`
    assert_conformant("[1, 2, 3].length()", "3").await;
    assert_conformant("[10, 20, 30].nth(1)", "20").await;
    assert_conformant("[1, 2, 3].concat([4])", "[1, 2, 3, 4]").await;
    assert_conformant(r#""abc".length()"#, "3").await;
    assert_conformant(r#""con".concat("cat")"#, r#""concat""#).await;
    // set
    assert_conformant("Set(1, 2).add(3)", "Set(1, 2, 3)").await;
    assert_conformant("Set(1, 2).contains(1)", "true").await;
    assert_conformant("Set(1, 2).size()", "2").await;
    assert_conformant("Set(1, 2).union(Set(3))", "Set(1, 2, 3)").await;
    assert_conformant("Set(1, 2).delete(1)", "Set(2)").await;
    assert_conformant("Set(1, 2).diff(Set(1))", "Set(2)").await;
    // map
    assert_conformant("{1 : 10}.get(1)", "10").await;
    assert_conformant("{1 : 10}.set(2, 20)", "{1:10, 2:20}").await;
    assert_conformant("{1 : 10}.contains(1)", "true").await;
    assert_conformant("{1 : 10}.size()", "1").await;
    assert_conformant("{1 : 10}.keys()", "Set(1)").await;
    assert_conformant("{1 : 10}.delete(1)", "{}").await;
    assert_conformant("{1 : 10}.union({2 : 20})", "{1:10, 2:20}").await;
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
        (
            r#"@("c")!([424242, 7, 7]) | for (@x <- @("c")) { @("OUT")!(x.length()) }"#,
            "3",
        ),
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
            observed.iter().map(render_as_rhocalc).collect::<Vec<_>>(),
            vec![expected.to_string()],
            "C1: {program:?} — a COMM-bound receiver must dispatch exactly like a literal one"
        );
    }
}

/// **★ Divergence L (NEW, discovered by C1's ordering check 2026-07-26) — RhoCalc sorts a
/// `Set`/`Map` LEXICOGRAPHICALLY by rendered element; Rholang sorts by `ScoredTerm` VALUE.**
///
/// The two orders coincide on every fixture the suite had before today, which is why this survived
/// unmeasured: they differ only when the rendered forms compare differently from the values, and
/// the smallest such case is **integers of unequal digit count**. `"10" < "2"` as text, `2 < 10`
/// as numbers.
///
/// ⚠ **This is NOT caused by C1, and the first row proves it.** `Set(10, 2)` is a bare literal
/// with no method call anywhere in it — nothing C1 touched can be involved — and it already
/// renders differently on the two sides. The divergence lives in the collection LITERAL: RhoCalc's
/// own `Set`/`Map` carrier orders its elements one way and `lower_set`/`lower_map` hand the
/// reducer a collection it then sorts its own way (`models/src/rust/sorted_par_hash_set.rs`).
///
/// What C1 owes here is therefore *consistency, not agreement*: a routed method must return its
/// result in the SAME order the literal already lands in, so routing introduces no NEW ordering
/// behaviour. That is what the second half asserts.
///
/// The reducer is normative, so `Set(2, 10)` is the right answer and RhoCalc's rendering is the
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
            "L: {source:?} — RhoCalc orders by the RENDERED element"
        );
        let observed = reduce(&proc).await.expect("the literal lowers");
        assert_eq!(
            observed.iter().map(render_as_rhocalc).collect::<Vec<_>>(),
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
        let observed = reduce(&parse(source)).await.expect("the routed method reduces");
        assert_eq!(
            observed.iter().map(render_as_rhocalc).collect::<Vec<_>>(),
            vec![machine_order.to_string()],
            "L: {source:?} — a routed result carries the reducer's canonical order"
        );
    }

    // ③ Where the two orders COINCIDE, the routed method and the fold agree outright — so the
    //    divergence really is about ordering and not about the values themselves.
    assert_conformant("Set(3, 2, 1).add(4)", "Set(1, 2, 3, 4)").await;
    assert_conformant(r#"Set("b", "a").add("c")"#, r#"Set("a", "b", "c")"#).await;
    // A List is ordered, not sorted, so it is order-stable on both sides by construction.
    assert_conformant("[10, 2].concat([3])", "[10, 2, 3]").await;
}

// ════════════════════════════════════════════════════════════════════════════════════════════════
// PART 5 — the adapter's own unit tests
// ════════════════════════════════════════════════════════════════════════════════════════════════

/// [`render_fixed_point`] implements RhoCalc's `Fixed` surface form; pin it directly so a
/// conformance failure is never mis-attributed to the adapter.
#[test]
fn render_fixed_point_matches_the_rhocalc_surface_form() {
    assert_eq!(render_fixed_point(&[3], 0), "3p0");
    assert_eq!(render_fixed_point(&[33], 1), "3.3p1");
    assert_eq!(render_fixed_point(&[100], 2), "1.00p2");
    // Fewer digits than the scale ⇒ a leading zero is synthesized.
    assert_eq!(render_fixed_point(&[5], 2), "0.05p2");
    // Negative unscaled values keep the sign outside the digit group.
    assert_eq!(render_fixed_point(&[0xCD], 1), "-5.1p1"); // 0xCD = -51
}

/// The ground-scalar arms of [`render_as_rhocalc`].
#[test]
fn render_as_rhocalc_matches_the_rhocalc_surface_form() {
    assert_eq!(render_as_rhocalc(&RuntimeObservationValue::Int(-3)), "-3");
    // ★ The `n` tail (divergence I, Stage C): `GBigInt`'s RhoCalc surface form REQUIRES it —
    // `-7` is the surface form of the `Int` `-7`, a different carrier.
    assert_eq!(
        render_as_rhocalc(&RuntimeObservationValue::BigIntBytes(vec![249])),
        "-7n"
    );
    assert_eq!(render_as_rhocalc(&RuntimeObservationValue::Bool(false)), "false");
    assert_eq!(
        render_as_rhocalc(&RuntimeObservationValue::Text("a\"b".to_string())),
        "\"a\\\"b\""
    );
    assert_eq!(
        render_as_rhocalc(&RuntimeObservationValue::DoubleBits(4.0_f64.to_bits())),
        "4.0"
    );
    assert_eq!(
        render_as_rhocalc(&RuntimeObservationValue::List(vec![
            RuntimeObservationValue::Int(1),
            RuntimeObservationValue::Int(2),
        ])),
        "[1, 2]"
    );
    assert_eq!(
        render_as_rhocalc(&RuntimeObservationValue::List(vec![
            RuntimeObservationValue::BigIntBytes(vec![1]),
            RuntimeObservationValue::BigIntBytes(vec![2]),
        ])),
        "[1n, 2n]"
    );
    assert_eq!(
        render_as_rhocalc(&RuntimeObservationValue::Map(vec![(
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
            observed.iter().map(render_as_rhocalc).collect::<Vec<_>>(),
            vec![r#""fired""#.to_string()],
            "K: the MACHINE fires {guard:?} on {datum:?} — that is the whole point of the \
             divergence, and if it stops firing the reducer's guard semantics changed"
        );
    }
}

/// **Divergence K (target) — the guard lane's normal form agrees with the machine.**
///
/// The reducer is NORMATIVE ("rhocalc IS rholang"), so where the two disagree the host is
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
            observed.iter().map(render_as_rhocalc).collect::<Vec<_>>()
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
/// right operand that the host nevertheless declines. RhoCalc spells `or` at TWO levels, and
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
/// (`rhocalc_ast.rs`'s `Matches` arm): the target is evaluated, the pattern is handed verbatim to
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
    use mettail_languages::rhocalc::formula::{
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
            observed.iter().map(render_as_rhocalc).collect::<Vec<_>>()
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
        observed.iter().map(render_as_rhocalc).collect::<Vec<_>>(),
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
//   | mettail / RhoCalc                | `Err(())` = **stuck**           |
//
// Mistranslating this does not raise an error — it LOOPS FOREVER. `pathmap`'s `to_next_val()`
// RESETS the zipper to the root when the walk finishes (`pathmap/src/zipper.rs:546`), so the
// position handed back on exhaustion is a perfectly valid ROOT zipper. Anything that surfaced it
// as a usable `ReadZipper` would silently restart the counted walk from the first leaf and never
// terminate, with nothing anywhere reporting a fault.
//
// The contract is pinned on both sides by tests that name each other:
//   * f1r3node: `rholang/tests/zipper_enumeration_spec.rs::to_next_leaf_returns_nil_when_exhausted`
//   * mettail:  `languages/src/rhocalc/zipper.rs::exhausted_walk_is_stuck_here_and_nil_on_the_reducer`
//     (and the surface-level `languages/tests/rhocalc_tests.rs::zipper_leaf_walk_exhaustion_stays_stuck`)
//
// This section is C1's half: it proves the property END-TO-END against the REAL reducer, over the
// exact `EMethod` chain the C1b lowering emits, and BOUNDED so a violation FAILS instead of
// hanging the suite.
// ════════════════════════════════════════════════════════════════════════════════════════════════

use models::rhoapi::expr::ExprInstance as ZExprInstance;
use models::rhoapi::{EEq as ZEEq, EList as ZEList, EMethod as ZEMethod, EPathMap as ZEPathMap};
use models::rhoapi::Expr as ZExpr;

fn zipper_expr_par(instance: ZExprInstance) -> Par {
    Par::default().with_exprs(vec![ZExpr { expr_instance: Some(instance) }])
}

/// A ground `EPathMap` over the given elements. In Rholang a PathMap element is BOTH the key and
/// the value it stores, which is why `getLeaf()` at a leaf returns the same list `getPath()` does.
///
/// ★ This is the C4 STAND-IN. RhoCalc source cannot produce an `EPathmapBody` today — a `Pathmap`
/// literal lowers to `EMap` (divergence G), which is exactly what
/// [`c1b_pathmap_zipper_family_is_c4_blocked_at_the_carrier`] measures. Building the carrier here
/// exercises the routed method names against the real reducer NOW, so that when C4 lands the
/// contract is already proved rather than discovered.
fn zipper_epathmap(elements: Vec<Par>) -> Par {
    zipper_expr_par(ZExprInstance::EPathmapBody(ZEPathMap::new(
        elements,
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
/// `rhocalc_ast.rs::lower_method` emits for the routed zipper family.
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
    let mut par = lower_rhocalc_proc(&scaffold).expect("the @(\"OUT\")!(Nil) scaffold lowers");
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

/// `m.readZipper()` followed by `steps` × `.toNextLeaf()`.
fn leaf_walk(steps: usize) -> Par {
    let mut zipper = zipper_method("readZipper", four_leaf_pathmap(), Vec::new());
    for _ in 0..steps {
        zipper = zipper_method("toNextLeaf", zipper, Vec::new());
    }
    zipper
}

/// `walk == Nil` — the reducer's own exhaustion test, as a `GBool`.
fn walk_is_nil(steps: usize) -> Par {
    zipper_expr_par(ZExprInstance::EEqBody(ZEEq {
        p1: Some(leaf_walk(steps)),
        p2: Some(Par::default()),
    }))
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
    // The DECIDABLE BOUND. A stuck term is not an end-test, which is precisely why `leafCount()`
    // exists and why it — not a "did it fail?" probe — is what terminates a counted walk.
    let counted = reduce_expression(zipper_method("leafCount", leaf_walk(0), Vec::new()))
        .await
        .expect("leafCount() at the root reduces");
    assert_eq!(
        counted.iter().map(render_as_rhocalc).collect::<Vec<_>>(),
        vec!["4".to_string()],
        "leafCount() at the root is the map's cardinality"
    );
    let leaf_count = 4usize;

    // Bounded search for the first exhausted step. `+ 1` is the whole budget: one step per leaf,
    // plus the step that falls off the end.
    let mut first_nil_at = None;
    for steps in 1..=(leaf_count + 1) {
        let observed = reduce_expression(walk_is_nil(steps))
            .await
            .expect("`walk == Nil` reduces to a Bool at every step in range");
        let rendered = observed.iter().map(render_as_rhocalc).collect::<Vec<_>>();
        assert_eq!(rendered.len(), 1, "step {steps}: expected exactly one Bool observation");
        match rendered[0].as_str() {
            "true" => {
                first_nil_at = Some(steps);
                break;
            },
            "false" => continue,
            other => panic!("step {steps}: `walk == Nil` must be a Bool, got {other:?}"),
        }
    }

    assert_eq!(
        first_nil_at,
        Some(leaf_count + 1),
        "★ EXHAUSTION CONTRACT VIOLATED. The walk must become Nil at exactly leafCount()+1 = {}. \
         `None` here means it never exhausted within the bound — i.e. the walk RESTARTED, which is \
         the infinite loop this test exists to catch (`to_next_val` resets to the root on \
         exhaustion). A smaller value means the walk ended early and entries were skipped.",
        leaf_count + 1
    );
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
            observed.iter().map(render_as_rhocalc).collect::<Vec<_>>(),
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
#[tokio::test(flavor = "multi_thread")]
async fn c1_zipper_walk_cannot_continue_past_exhaustion() {
    let leaf_count = 4usize;

    // `toNextLeaf()` ON the exhausted Nil.
    let stepped = reduce_expression(leaf_walk(leaf_count + 2)).await;
    assert!(
        stepped.is_err(),
        "★ stepping past exhaustion must FAIL. Getting a value here means the walk restarted from \
         the root — the infinite loop. Got {stepped:?}"
    );

    // `getPath()` ON the exhausted Nil — the accessor a walk body would call.
    let path = reduce_expression(zipper_method("getPath", leaf_walk(leaf_count + 1), Vec::new()))
        .await;
    assert!(
        path.is_err(),
        "★ reading a path out of the exhausted Nil must FAIL, not answer the first leaf. Got {path:?}"
    );
}

/// **The RhoCalc side of the same fixture still reports exhaustion as STUCK — the two conventions,
/// measured side by side.**
///
/// The fold path is unchanged by C1, and this pins that the mismatch documented in
/// `languages/src/rhocalc/zipper.rs` is still exactly what it says it is: where the reducer
/// answers `Nil`, RhoCalc's `.toNextLeaf()` leaves the term unreduced. A stuck term still DISPLAYS
/// the method call, which is how "stuck" is observed here.
#[tokio::test(flavor = "multi_thread")]
async fn c1_rhocalc_side_still_reports_exhaustion_as_stuck() {
    // Two entries, so the third step is one past the end.
    let source = "{| 1 : 10, 2 : 20 |}.readZipper().toNextLeaf().toNextLeaf().toNextLeaf()";
    let residue = fold(&parse(source)).expect("the fold converges");
    assert!(
        residue.contains("toNextLeaf"),
        "the exhausted RhoCalc walk must stay STUCK (the call survives in the normal form), which \
         is the convention the reducer's Nil has to be translated FROM. Got {residue:?}"
    );
}


/// **★ Every routed zipper/pathmap method is exercised against a REAL `EPathMap` — the check that
/// caught `setLeaf`.**
///
/// A shared method NAME is not a shared operation, and this family is the one place where that
/// cannot be checked by the ordinary conformance rows: `Pathmap` lowers to `EMap`, so none of these
/// calls can reach their carrier from RhoCalc source until C4
/// ([`c1b_pathmap_zipper_family_is_c4_blocked_at_the_carrier`]). Without this test the entire
/// family would be routed on the strength of name matching alone.
///
/// It already earned its keep. `setLeaf` is **not** in the list below because this check found that
/// RhoCalc's `w.setLeaf(full, v)` writes at an ABSOLUTE PATH ARGUMENT while Rholang's
/// `z.setLeaf(v)` writes at the zipper's FOCUS and takes one argument — the same name, a different
/// operation, and an arity mismatch that would otherwise have shipped as a latent bug. It is left
/// fail-closed and named in `rhocalc_ast.rs::unsupported_construct_name`.
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
            observed.iter().map(render_as_rhocalc).collect::<Vec<_>>(),
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
