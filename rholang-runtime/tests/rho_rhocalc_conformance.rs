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
//! | **C** | `l.nth(i)` out of bounds, and `nth` on a plain (`BigInt`) index | **process abort** / `error` | recoverable `ReduceError` | C1 | open |
//! | **D** | `Fixed` arithmetic on **mismatched scales** | rescales | `OperatorExpectedError` | C1 | open |
//! | **E** | canonical **collection order** for `toByteArray` | protobuf byte order | `ScoredTerm` value order | C2 | ★ CLOSED |
//! | **F** | `.toByteArray()` | a hex `GString` — and unreachable from source | a real `GByteArray` | C2 | ★ CLOSED |
//! | **G** | `Pathmap` / zippers | own carriers + 20+ methods | `EPathmapBody`/`EZipperBody` exist, unused | C4 | open |
//! | **H** | `==` / `!=` on **`Bool`** | `error` (no fold arm) | `Bool(true)` | C1 | open |
//!
//! `H` was **discovered by this suite** — it is not in the original `§17.11` inventory.
//!
//! ### ⚠ The pins this suite replaces did not pin anything
//!
//! `languages/tests/rhocalc_tests.rs::assert_reduces_to` — the helper behind most of that file's
//! RhoCalc semantics tests — reaches its verdict through a disjunction that ends in
//! `bag_multiset_eq(nf, expected)`, and `bag_multiset_eq` returns
//! `to_sorted_bag_elements(a) == to_sorted_bag_elements(b)`, i.e. `None == None` ⟹ **`true`**,
//! whenever neither side is a `#{…}#` bag literal. Measured 2026-07-25:
//! `assert_reduces_to("1 + 2", "999")` **passes**. Guarding the comparator turns **39 of that
//! file's 412 tests** red. That is why this suite compares with `assert_eq!` on an explicitly
//! written expected value and never through a fuzzy helper.
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
//! error 5, aborting`. Divergence C's panic is therefore proven by **re-executing this test binary
//! as a child process** and asserting the child's death — see
//! [`divergence_c_witness_out_of_bounds_nth_aborts_the_process`].

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
    let definitions = fold_definitions_for(&take_held_fold_sites());
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
        // `int(a, w)` — the fixed-width `Int` category ⟷ `ExprInstance::GInt`.
        RuntimeObservationValue::Int(literal) => literal.to_string(),
        // A plain RhoCalc integer literal is arbitrary-precision (Rholang 1.4's default), so it
        // rides as `GBigInt` — signed big-endian two's-complement bytes.
        RuntimeObservationValue::BigIntBytes(bytes) => {
            num_bigint::BigInt::from_signed_bytes_be(bytes).to_string()
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

/// Arbitrary-precision integer arithmetic. A plain RhoCalc integer literal is `BigInt`
/// (Rholang 1.4's default), so these ride `GBigInt` on the machine and `CanonicalBigInt` in the
/// fold — different carriers, one value.
#[tokio::test(flavor = "multi_thread")]
async fn conformance_bigint_arithmetic() {
    assert_conformant("1 + 2", "3").await;
    assert_conformant("5 - 3", "2").await;
    assert_conformant("3 * 4", "12").await;
    assert_conformant("10 / 2", "5").await;
    assert_conformant("10 % 3", "1").await;
    assert_conformant("-7", "-7").await;
    assert_conformant("0 - 2", "-2").await;
    assert_conformant("1n + 2n", "3").await;
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

/// The environment variable that arms [`zz_divergence_c_out_of_bounds_nth_probe`]. Without it the
/// probe is inert, so even `cargo nextest run --run-ignored all` cannot trip the abort.
const DIVERGENCE_C_PROBE_ARMED: &str = "MTL_DIVERGENCE_C_PROBE";

/// **Divergence C (witness, part 1) — out-of-bounds `nth` ABORTS the process.**
///
/// `languages/src/rhocalc.rs` `LNth` body ends in `v.get(*n as usize).cloned().expect("at: index
/// out of bounds")` — a Rust panic. Rholang instead returns a recoverable
/// `InterpreterError::ReduceError("Error: index out of bound: N")`
/// (`rholang/src/rust/interpreter/reduce.rs:4073-4081`).
///
/// The panic cannot be caught in-process (see the module header: unwinding across this workspace's
/// Cranelift frames aborts with `failed to initiate panic, error 5`), so it is proven by
/// re-executing THIS test binary for the armed probe below and asserting the child's death.
///
/// *Delete when C1 lands* (the fold body is gone; `nth` becomes `EMethod("nth")`).
#[test]
fn divergence_c_witness_out_of_bounds_nth_aborts_the_process() {
    let binary = std::env::current_exe().expect("the running test binary path");
    let output = std::process::Command::new(binary)
        .args([
            "--exact",
            "zz_divergence_c_out_of_bounds_nth_probe",
            "--ignored",
            "--nocapture",
            "--test-threads",
            "1",
        ])
        .env(DIVERGENCE_C_PROBE_ARMED, "1")
        .output()
        .expect("re-execute this test binary for the armed out-of-bounds probe");

    assert!(
        !output.status.success(),
        "C: `[1,2,3].nth(int(10,64))` must still be observed to kill the process \
         (status {:?}); if it no longer does, C1 has landed and this witness must be deleted",
        output.status
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("index out of bounds"),
        "C: the child must die on the RhoCalc fold's `.expect(\"at: index out of bounds\")`, \
         got stderr:\n{stderr}"
    );
}

/// The armed probe re-executed by [`divergence_c_witness_out_of_bounds_nth_aborts_the_process`].
/// Inert unless [`DIVERGENCE_C_PROBE_ARMED`] is set, so it is safe under `--run-ignored all`.
#[test]
#[ignore = "divergence C probe: ABORTS the process when armed; driven as a child process by \
            divergence_c_witness_out_of_bounds_nth_aborts_the_process"]
fn zz_divergence_c_out_of_bounds_nth_probe() {
    if std::env::var_os(DIVERGENCE_C_PROBE_ARMED).is_none() {
        return;
    }
    let proc = parse("[1, 2, 3].nth(int(10, 64))");
    let _ = fold(&proc);
    unreachable!("the RhoCalc `nth` fold must have aborted the process");
}

/// **Divergence C (witness, part 2) — `nth` does not even accept RhoCalc's own default integer.**
///
/// `LNth`'s fold body matches `(Proc::CastList(_), Proc::CastInt(_))`, but a plain RhoCalc integer
/// literal is `BigInt` — so `[1,2,3].nth(0)` folds to `error` while `[1,2,3].nth(int(0,64))`
/// folds to `1`. The machine has no such carrier restriction: `reduce.rs:4106-4118` accepts
/// `EList`, `ETuple` **and** `GByteArray` receivers with an `eval_to_i64` index.
///
/// *Delete when C1 lands.*
#[tokio::test(flavor = "multi_thread")]
async fn divergence_c_witness_nth_rejects_a_plain_integer_index() {
    assert_eq!(
        fold(&parse("[1, 2, 3].nth(0)")).expect("the fold converges"),
        "error",
        "C: the fold's `nth` requires the fixed-width `Int` carrier, not RhoCalc's default BigInt"
    );
    assert_eq!(
        fold(&parse("[1, 2, 3].nth(int(0, 64))")).expect("the fold converges"),
        "1",
        "C: the same index, cast to the fixed-width carrier, works — proving it is a CARRIER \
         restriction, not a bounds check"
    );
    let err = reduce(&parse("[1, 2, 3].nth(0)"))
        .await
        .expect_err("the method is not lowered at all today");
    assert_eq!(err, "unsupported: l.nth(i) list method");
}

/// **Divergence C (target) — `nth` is Rholang's `nth`: total on the carrier, recoverable on error.**
///
/// Closed by **C1** (`EMethodBody(EMethod { method_name: "nth", … })` against the reducer's own
/// method table, `reduce.rs:8197-8256`).
#[tokio::test(flavor = "multi_thread")]
#[ignore = "divergence C: `l.nth(i)` is UnsupportedProc on the machine and panics in the fold; \
            closed by C1 (route `nth` to EMethod)"]
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
/// The old goldens (`2a15a201120a042a0210020a042a0210040a042a021006` for `[1,2,3]`) therefore
/// encoded a **different Rholang term** than RhoCalc means: `GInt` elements (`sint64` zigzag
/// `02 04 06` = 1, 2, 3) where the real term carries `GBigInt` elements. The bytes asserted below
/// are the machine's, and they carry `9a 02 01 0N` — the `GBigInt` leaves — exactly as
/// `lower_list` emits them.
///
/// (The five golden-hex tests that pinned the fork lived in
/// `languages/tests/rhocalc_tests.rs::native_ops::collection_wire`. They were retired rather than
/// migrated because they asserted nothing: see that module's replacement comment for the measured
/// `assert_reduces_to` vacuity.)
#[tokio::test(flavor = "multi_thread")]
async fn c2_closed_to_byte_array_is_the_reducers_own_encoding() {
    for (source, expected) in [
        // A list of three arbitrary-precision integers: `EList` (field 20 ⟹ `a2 01`) of three
        // `Par`s each carrying one `GBigInt` (`9a 02`) leaf.
        (
            "[1, 2, 3].toByteArray()",
            "2a1ba201180a062a049a0201010a062a049a0201020a062a049a020103",
        ),
        // `ESet` (field 22 ⟹ `b2 01`). Source order is irrelevant — the machine canonicalizes
        // through `SortedParHashSet`, so both spellings give byte-identical output.
        (
            "Set(1, 2, 3).toByteArray()",
            "2a1bb201180a062a049a0201010a062a049a0201020a062a049a020103",
        ),
        (
            "Set(3, 2, 1).toByteArray()",
            "2a1bb201180a062a049a0201010a062a049a0201020a062a049a020103",
        ),
        // `EMap` (field 23 ⟹ `ba 01`), likewise order-independent.
        (
            "{1: 10, 2: 20}.toByteArray()",
            "2a27ba01240a100a062a049a02010112062a049a02010a0a100a062a049a02010212062a049a020114",
        ),
        (
            "{2: 20, 1: 10}.toByteArray()",
            "2a27ba01240a100a062a049a02010112062a049a02010a0a100a062a049a02010212062a049a020114",
        ),
        // Nesting rides through unchanged.
        (
            "[[1, 2], [3]].toByteArray()",
            "2a29a201260a152a13a201100a062a049a0201010a062a049a0201020a0d2a0ba201080a062a049a020103",
        ),
        // The empty list — the one case the retired fork also got right, since it has no elements
        // to mis-type. Byte-identical to the old golden `2a03a20100`.
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
/// `Set(0 - 2, 1)` is the discriminating case. Rholang's `ScoredTerm` order is by **value**, so
/// `-2` precedes `1`… but the observed encoding lists `GBigInt(01)` before `GBigInt(fe)`, because
/// `GBigInt` is scored on its signed big-endian **bytes**. Either way the answer is now produced
/// by exactly one implementation — the machine's `SortedParHashSet` — instead of by a second,
/// independently-sorted host encoder that could (and for negative members did) disagree.
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
        "2a13b201100a062a049a0201010a062a049a0201fe",
        "E: the member order is the machine's own (`01` then `fe` = 1 then -2)"
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
        "2a54a201510a1e3a1c0a1a0a180a166d65747461696c2e72686f63616c632e6261672e76310a2f2a2d\
         a2012a0a132a11a2010e0a062a049a0201010a042a0210020a132a11a2010e0a062a049a0201020a04\
         2a021004"
    );
}

// ── G — Pathmap and zipper carriers ──────────────────────────────────────────────────────────────

/// **Divergence G (witness) — `Pathmap` lowers to `EMap`, and every zipper method is unsupported.**
///
/// `rhoapi` already declares `e_pathmap_body = 32` and `e_zipper_body = 33`, and
/// `rholang/src/rust/interpreter/reduce.rs` already implements
/// `readZipper/writeZipper/descendTo/getLeaf/getSubtrie/graft/joinInto/ascend/childCount/…`. But
/// `rholang-runtime/src/rhocalc_ast.rs:1600-1624` lowers `Pathmap` to **`EMap`** — discarding the
/// trie structure — and `:1030-1048` marks every zipper method `UnsupportedProc`. So ~8 pathmap
/// and ~15 zipper methods are implemented twice MeTTaIL-side
/// (`languages/src/rhocalc/{pathmap,zipper}.rs`) and never reach their native counterpart.
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

    // Pathmap and zipper METHODS never reach the machine at all.
    for (source, expected_error) in [
        ("{|1:2|}.get(1)", "unsupported: m.get(k) map method"),
        ("{|1:2|}.union({|3:4|})", "unsupported: m.union(n) map method"),
        ("{|1:2|}.readZipper()", "unsupported: p.readZipper() zipper method"),
    ] {
        assert_eq!(
            reduce(&parse(source)).await.expect_err("not lowered"),
            expected_error,
            "G: {source:?}"
        );
    }
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

/// **Divergence H (witness) — `==` / `!=` on `Bool` folds to `error`.**
///
/// Discovered by this suite; not in the `§17.11` inventory. `languages/src/rhocalc.rs`'s `Eq`/`Ne`
/// fold bodies have no `Bool` arm, so `true == true` folds to `Proc::Err`, while the machine's
/// `relopb` (`reduce.rs:2755-2766`) answers `true`. The fold is *less* capable than the reducer
/// here, which is the benign direction — but it is still two implementations disagreeing.
///
/// *Delete when C1 lands.*
#[tokio::test(flavor = "multi_thread")]
async fn divergence_h_witness_boolean_equality_folds_to_error() {
    for (source, machine_answer) in [("true == true", "true"), ("true != false", "true")] {
        let proc = parse(source);
        assert_eq!(
            fold(&proc).expect("the fold converges"),
            "error",
            "H: {source:?} — the fold has no Bool arm for `==`/`!=`"
        );
        let observed = reduce(&proc).await.expect("the machine compares booleans");
        assert_eq!(
            observed.iter().map(render_as_rhocalc).collect::<Vec<_>>(),
            vec![machine_answer.to_string()],
            "H: {source:?} — reduce.rs's `relopb` answers it"
        );
    }
}

/// **Divergence H (target) — boolean equality agrees.**
///
/// Closed by **C1**.
#[tokio::test(flavor = "multi_thread")]
#[ignore = "divergence H: `true == true` folds to `error` while the reducer answers `true`; \
            closed by C1"]
async fn divergence_h_target_boolean_equality_agrees() {
    assert_conformant("true == true", "true").await;
    assert_conformant("true != false", "true").await;
    assert_conformant("true == false", "false").await;
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

/// **The C1 inventory (witness).** Every one of these methods is implemented *twice* — once as a
/// `![{…}]` fold body in `languages/src/rhocalc.rs` and once in `reduce.rs`'s method table
/// (`reduce.rs:8197-8256`) — yet the machine never sees them, because the lowering rejects the
/// construct. The fold answers are the current MeTTaIL semantics; the machine errors are the
/// current lowering gap.
///
/// This test IS the C1 work list: closing C1 means every row here lowers, and
/// [`c1_target_collection_methods_route_to_the_reducer`] replaces it.
///
/// *Delete when C1 lands.*
#[tokio::test(flavor = "multi_thread")]
async fn c1_inventory_witness_collection_methods_are_not_lowered() {
    for (source, fold_answer, machine_error) in [
        // list
        ("[1, 2, 3].length()", "3", "unsupported: l.length() list method"),
        ("[1, 2, 3].concat([4])", "[1, 2, 3, 4]", "unsupported: l.concat(m) list method"),
        // string (routed through the LIST method arms today)
        (r#""abc".length()"#, "3", "unsupported: l.length() list method"),
        (r#""con".concat("cat")"#, r#""concat""#, "unsupported: l.concat(m) list method"),
        // set
        ("Set(1, 2).add(3)", "Set(1, 2, 3)", "unsupported: s.add(e) set method"),
        ("Set(1, 2).contains(1)", "true", "unsupported: m.contains(k) map method"),
        ("Set(1, 2).size()", "2", "unsupported: m.size() map method"),
        ("Set(1, 2).union(Set(3))", "Set(1, 2, 3)", "unsupported: m.union(n) map method"),
        ("Set(1, 2).delete(1)", "Set(2)", "unsupported: m.delete(k) map method"),
        // map
        ("{1 : 10}.get(1)", "10", "unsupported: m.get(k) map method"),
        ("{1 : 10}.set(2, 20)", "{1:10, 2:20}", "unsupported: m.set(k, v) map method"),
        ("{1 : 10}.contains(1)", "true", "unsupported: m.contains(k) map method"),
        ("{1 : 10}.size()", "1", "unsupported: m.size() map method"),
        ("{1 : 10}.keys()", "Set(1)", "unsupported: m.keys() map method"),
        // `.values()` is NOT a C1 row — Rholang has no `values` method, so it is C3 residue.
        ("{1 : 10}.delete(1)", "{}", "unsupported: m.delete(k) map method"),
        ("{1 : 10}.union({2 : 20})", "{1:10, 2:20}", "unsupported: m.union(n) map method"),
    ] {
        let proc = parse(source);
        assert_eq!(
            fold(&proc).expect("the fold converges"),
            fold_answer,
            "C1: {source:?} — the duplicate MeTTaIL-side implementation"
        );
        assert_eq!(
            reduce(&proc).await.expect_err("the method is not lowered today"),
            machine_error,
            "C1: {source:?} — the machine never sees the method"
        );
    }
}

/// **The C1 target — every collection method is evaluated by the reducer's own method table.**
///
/// Closed by **C1** (`EMethodBody` emission + deleting the corresponding fold bodies). The values
/// asserted here are the ones both sides already agree on today, so a green run proves the
/// deletion preserved semantics rather than merely removing them.
#[tokio::test(flavor = "multi_thread")]
#[ignore = "C1: the 30+ collection/string methods are UnsupportedProc on the machine; closed by C1 \
            (route them to EMethodBody against reduce.rs's method table)"]
async fn c1_target_collection_methods_route_to_the_reducer() {
    assert_conformant("[1, 2, 3].length()", "3").await;
    assert_conformant("[1, 2, 3].concat([4])", "[1, 2, 3, 4]").await;
    assert_conformant(r#""abc".length()"#, "3").await;
    assert_conformant(r#""con".concat("cat")"#, r#""concat""#).await;
    assert_conformant("Set(1, 2).add(3)", "Set(1, 2, 3)").await;
    assert_conformant("Set(1, 2).contains(1)", "true").await;
    assert_conformant("Set(1, 2).size()", "2").await;
    assert_conformant("Set(1, 2).union(Set(3))", "Set(1, 2, 3)").await;
    assert_conformant("Set(1, 2).delete(1)", "Set(2)").await;
    assert_conformant("{1 : 10}.get(1)", "10").await;
    assert_conformant("{1 : 10}.set(2, 20)", "{1:10, 2:20}").await;
    assert_conformant("{1 : 10}.contains(1)", "true").await;
    assert_conformant("{1 : 10}.size()", "1").await;
    assert_conformant("{1 : 10}.keys()", "Set(1)").await;
    assert_conformant("{1 : 10}.union({2 : 20})", "{1:10, 2:20}").await;
    // `.values()` is NOT here: `reduce.rs::method_table` has `keys` but no `values`, so it is
    // MeTTaIL-only residue and belongs to C3 — see
    // `c3_residue_mettail_only_operations_fail_closed_and_named`.
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
    assert_eq!(
        render_as_rhocalc(&RuntimeObservationValue::BigIntBytes(vec![249])),
        "-7"
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
            RuntimeObservationValue::BigIntBytes(vec![1]),
            RuntimeObservationValue::BigIntBytes(vec![2]),
        ])),
        "[1, 2]"
    );
    assert_eq!(
        render_as_rhocalc(&RuntimeObservationValue::Map(vec![(
            RuntimeObservationValue::BigIntBytes(vec![1]),
            RuntimeObservationValue::BigIntBytes(vec![10]),
        )])),
        "{1:10}"
    );
}
