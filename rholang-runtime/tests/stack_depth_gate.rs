//! # The Θ(depth) regression gate for the RhoCalc **lowering**
//!
//! **The defect this gate exists for.** `rhocalc_ast::lower_proc` translates a
//! parsed RhoCalc `Proc` into a normalized `rhoapi::Par`. Before Stage M it did
//! so by *host recursion*: one native frame per nesting level of the term. A
//! 30-byte program — `@"OUT"!([[[[…[1]…]]]])` — therefore aborted the process,
//! because a stack overflow is a `SIGSEGV` delivered on the guard page, not a
//! catchable error.
//!
//! Located under `gdb` on 2026-07-27:
//!
//! ```text
//! Thread 1 "rhocalc" received signal SIGSEGV, Segmentation fault.
//! mettail_rholang_runtime::rhocalc_ast::lower_proc () at rholang-runtime/src/rhocalc_ast.rs:931
//! Backtrace stopped: Cannot access memory        ← the guard page
//! ```
//!
//! ## ★ Why `RUST_MIN_STACK` is INERT on this path, and why this gate does not use it
//!
//! `rholang-runtime/src/bin/rhocalc.rs` is `#[tokio::main] async fn main`, so
//! parsing and lowering run on the process's **main** thread. `RUST_MIN_STACK`
//! is read only by `std::thread`'s spawn path — it cannot resize a main thread,
//! whose size is fixed by `ulimit -s` before `main` is entered. A sweep of
//! `RUST_MIN_STACK` from 1 MiB to 32 MiB against the reproducer reported "ok" at
//! every value **because it was controlling nothing**.
//!
//! That is exactly why every subject here runs on a thread created with an
//! explicit [`std::thread::Builder::stack_size`]: it is the one mechanism that
//! binds regardless of how the code under test is *reached* in production, so
//! neither `RUST_MIN_STACK` nor `ulimit -s` can mask a regression.
//!
//! ## Two axes, not one
//!
//! A traversal can grow with term **nesting** (`[[[…]]]`) or with sibling
//! **width** (`[a, b, c, …]`). `lower_proc`'s list arm delegates to
//! [`lower_list`], which iterates its elements — so the width axis is expected
//! to be flat — but "expected" is not "measured", and a future arm that folds a
//! sibling list recursively would be invisible to a depth-only ladder. Every
//! subject therefore has a depth ladder and, where the shape admits one, a
//! width ladder.
//!
//! ## Why a fixed-stack ladder alone is NOT sufficient
//!
//! A traversal with a large intercept and a small slope passes a fixed-stack
//! ladder while still being Θ(depth). f1r3node's sibling gate measured exactly
//! this: `compare_score` at 1,329 B/level with a ~40 KiB intercept needs 381 KiB
//! at depth 256, comfortably inside a 1 MiB fixed stack. So the real assertion
//! is [`assert_no_slope`], which bisects the minimum viable stack at *both ends*
//! of a wide ladder (4 → 4,096 on depth, 4 → 65,536 on width) and requires no growth.
//! It compares a traversal against **itself**, so it is profile-independent by
//! construction — it asserts a *shape*, never a byte count.
//!
//! ## ⚠ Why the tripwire's constants are per-profile
//!
//! Frame sizes differ several-fold between profiles because `rustc` does not
//! overlay the stack slots of mutually exclusive `match` arms at `-O0`, and this
//! crate additionally sets `codegen-backend = "cranelift"` for `[profile.dev]`.
//! Only [`assert_slope_below`] takes ceilings, and it selects them per profile
//! via `cfg!(debug_assertions)`.
//!
//! ## ⚠ Probing has to FORK
//!
//! A stack overflow is a `SIGSEGV` caught by the runtime's guard-page handler,
//! which prints and `abort()`s. It is not a panic and not unwindable, so a probe
//! that overflows in-process takes the whole test binary with it — every
//! assertion that had already passed included. Each probe therefore runs in a
//! CHILD process: the gate re-execs its own test binary with `GATE_SUBJECT` /
//! `GATE_DEPTH` / `GATE_STACK` set and reads the exit status. 0 = survived.
//!
//! ## ⚠ Teardown is a DIFFERENT traversal, and only ONE side of it needs help
//!
//! Both the input and the output of a lowering are deeply nested trees, and a
//! *recursive* `Drop` on either would make every reading `max(lowering, drop)` —
//! keeping this gate red for a reason that has nothing to do with the lowering.
//! The two sides are not in the same state, and the asymmetry is the finding:
//!
//! * **`Proc` (the input) is already safe.** The `language!` macro generates a
//!   hand-written *iterative* `Drop` for the whole AST family — a pooled
//!   `DropTask` worklist with a re-entrancy flag
//!   (`target/generated/rhocalc/iterative_drop.rs`). So `drop(term)` is O(1) in
//!   stack and needs nothing from this file. (It also means a `Proc` cannot be
//!   destructured by value at all — `E0509`, cannot move out of a type that
//!   implements `Drop` — so a hand-rolled teardown here is not merely redundant,
//!   it does not compile.)
//! * **`Par` (the output) is not.** It is a `prost` message tree with a *derived*
//!   recursive `Drop`, so subjects tear it down with
//!   `models::rust::rholang::par_children::dismantle`, f1r3node's own iterative
//!   teardown, written for exactly this reason.
//!
//! ★ Worth stating because it frames Stage M: mettail's AST family had already
//! been converted to heap-bounded traversals. The **lowering** — the bridge from
//! that family to `rhoapi::Par` — had not.
#![cfg(feature = "rhocalc-runtime")]

use std::sync::Arc;

use mettail_languages::rhocalc::{Int, List, Proc};
use mettail_rholang_runtime::rhocalc_ast::{lower_proc_in_env, BoundEnv};
use models::rust::rholang::par_children::dismantle;

// ---------------------------------------------------------------------------
// term construction — ITERATIVE, so the builder itself is never the constraint
// ---------------------------------------------------------------------------

fn int(n: i64) -> Proc {
    Proc::CastInt(Arc::new(Int::NumLit(n)))
}

fn list(items: Vec<Proc>) -> Proc {
    Proc::CastList(Arc::new(List::ListLit(items)))
}

/// `[[[…[1]…]]]` with `depth` bracket levels — the reported shape.
fn nested_list(depth: usize) -> Proc {
    let mut p = int(1);
    for _ in 0..depth {
        p = list(vec![p]);
    }
    p
}

/// `[0, 1, …, width-1]` — the WIDTH counterpart of [`nested_list`].
fn wide_list(width: usize) -> Proc {
    let mut items = Vec::with_capacity(width);
    for i in 0..width {
        items.push(int(i as i64));
    }
    list(items)
}

/// `(((…(1 + 1)… + 1) + 1)` with `depth` additions: a chain through the BINARY
/// arithmetic arms rather than the collection arm, so a conversion that flattens
/// only `CastList` cannot pass by accident.
fn nested_add(depth: usize) -> Proc {
    let mut p = int(1);
    for _ in 0..depth {
        p = Proc::Add(Arc::new(p), Arc::new(int(1)));
    }
    p
}

/// `a | (b | (c | …))` with `depth` levels: the `PParInfix` arm, which recurses
/// on BOTH operands.
fn nested_par(depth: usize) -> Proc {
    let mut p = Proc::PZero;
    for _ in 0..depth {
        p = Proc::PParInfix(Arc::new(Proc::PZero), Arc::new(p));
    }
    p
}

/// The reported reproducer as a SOURCE string: `@"OUT"!([[[…[1]…]]])`.
fn reproducer_source(depth: usize) -> String {
    // 8 chars of frame + 2 chars per level + a digit; preallocate exactly.
    let mut s = String::with_capacity(2 * depth + 16);
    s.push_str("@\"OUT\"!(");
    for _ in 0..depth {
        s.push('[');
    }
    s.push('1');
    for _ in 0..depth {
        s.push(']');
    }
    s.push(')');
    s
}

// ---------------------------------------------------------------------------
// teardown
//
// `Proc` needs none: the `language!` macro gives the AST family a pooled,
// iterative `Drop` (see the module header). `Par` does, and gets f1r3node's.
// ---------------------------------------------------------------------------

/// Drop a lowered `Proc` on the gated thread.
///
/// A plain `drop`, deliberately — and the fact that a plain `drop` is *correct*
/// here is itself part of what this gate asserts. If the generated iterative
/// `Drop` were ever replaced by derived glue, every depth subject below would
/// start showing a slope, and the gate would go red without needing a new
/// subject to notice it.
fn release(term: Proc) {
    drop(term);
}

// ---------------------------------------------------------------------------
// subjects
// ---------------------------------------------------------------------------

fn lower(term: Proc) {
    let env = BoundEnv::new();
    let par = lower_proc_in_env(&term, &env).expect("stack_depth_gate: lowering failed");
    dismantle(par);
    release(term);
}

fn lower_depth_body(depth: usize) {
    lower(nested_list(depth));
}

fn lower_width_body(width: usize) {
    lower(wide_list(width));
}

fn lower_add_body(depth: usize) {
    lower(nested_add(depth));
}

fn lower_par_body(depth: usize) {
    lower(nested_par(depth));
}

/// The reported reproducer end-to-end: PARSE the source, then lower it. This is
/// the subject that reproduces the `SIGSEGV`, and it is the only one that has
/// the parser in its path on purpose.
fn reproducer_body(depth: usize) {
    let source = reproducer_source(depth);
    let term = Proc::parse_via_wpda(&source).expect("stack_depth_gate: reproducer did not parse");
    lower(term);
}

/// **M-6 — the PARSER's own constant.** It is not binding at the depths the
/// lowering used to fault at, but "not binding" and "not present" are different
/// claims, and only one of them had been measured. Subject the parser alone, so
/// its slope is a number in the ledger rather than an assumption.
fn parse_depth_body(depth: usize) {
    let source = reproducer_source(depth);
    let term = Proc::parse_via_wpda(&source).expect("stack_depth_gate: reproducer did not parse");
    release(term);
}

fn parse_width_body(width: usize) {
    let mut s = String::with_capacity(4 * width + 16);
    s.push_str("@\"OUT\"!([");
    for i in 0..width {
        if i > 0 {
            s.push_str(", ");
        }
        s.push_str(&i.to_string());
    }
    s.push_str("])");
    let term = Proc::parse_via_wpda(&s).expect("stack_depth_gate: wide source did not parse");
    release(term);
}

/// Names the subject a child process should run. Kept in one place so the parent
/// and the child cannot drift.
///
/// `GATE_DEPTH` means *nesting* for the depth subjects and *sibling count* for
/// the `*_wide` subjects.
fn subject(name: &str) -> fn(usize) {
    match name {
        // -------- depth axis --------
        "lower_depth" => lower_depth_body,
        "lower_add" => lower_add_body,
        "lower_par" => lower_par_body,
        "reproducer" => reproducer_body,
        "parse_depth" => parse_depth_body,
        // -------- width axis --------
        "lower_width" => lower_width_body,
        "parse_width" => parse_width_body,
        other => panic!("stack_depth_gate: unknown GATE_SUBJECT={:?}", other),
    }
}

// ---------------------------------------------------------------------------
// the child / probe mechanism
// ---------------------------------------------------------------------------

/// The child entry point. `#[ignore]`d so a normal run never executes it
/// directly; the parent always invokes it explicitly.
///
/// ⚠ It must be a NO-OP when its environment is absent. `cargo nextest run
/// --run-ignored all` will run every `#[ignore]`d test, including this one, with
/// no `GATE_SUBJECT` set — so a child entry point that *required* its environment
/// would fail the suite for a reason that has nothing to do with the property
/// being gated. Skipping is correct here precisely because this test is a
/// mechanism, not an assertion: the assertions live in its callers.
#[test]
#[ignore = "child process of the gate; driven via GATE_SUBJECT"]
fn gate_child() {
    let Ok(name) = std::env::var("GATE_SUBJECT") else {
        println!("gate_child: no GATE_SUBJECT — not a child invocation, nothing to do");
        return;
    };
    let depth: usize = std::env::var("GATE_DEPTH")
        .expect("GATE_DEPTH must accompany GATE_SUBJECT")
        .parse()
        .expect("GATE_DEPTH must be an integer");
    let stack: usize = std::env::var("GATE_STACK")
        .expect("GATE_STACK must accompany GATE_SUBJECT")
        .parse()
        .expect("GATE_STACK must be an integer");

    std::thread::Builder::new()
        .stack_size(stack)
        .name("gate".to_string())
        .spawn(move || subject(&name)(depth))
        .expect("stack_depth_gate: failed to spawn")
        .join()
        .expect("stack_depth_gate: subject panicked");
}

/// Run one probe point in a child process. `true` iff it survived.
fn runs_within(stack: usize, depth: usize, subject_name: &str) -> bool {
    let exe = std::env::current_exe().expect("stack_depth_gate: current_exe");
    std::process::Command::new(exe)
        .args(["--ignored", "--exact", "gate_child"])
        .env("GATE_SUBJECT", subject_name)
        .env("GATE_DEPTH", depth.to_string())
        .env("GATE_STACK", stack.to_string())
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .status()
        .expect("stack_depth_gate: failed to run child")
        .success()
}

/// Bisection resolution, in bytes. Both the zero-slope tolerance and the
/// tripwire's derived slope are quantised to this.
const RESOLUTION: usize = 4096;

/// Smallest stack (to [`RESOLUTION`] granularity) on which `name` survives at
/// `depth`. Exponential probe, then bisect.
fn min_stack_for(name: &str, depth: usize) -> usize {
    let mut hi = 16 * 1024;
    while hi <= 512 * 1024 * 1024 && !runs_within(hi, depth, name) {
        hi *= 2;
    }
    assert!(
        hi <= 512 * 1024 * 1024,
        "`{}` needed more than 512 MiB at parameter {}",
        name,
        depth
    );
    let mut lo = hi / 2;
    while hi - lo > RESOLUTION {
        let mid = (lo + hi) / 2;
        if runs_within(mid, depth, name) {
            hi = mid;
        } else {
            lo = mid;
        }
    }
    hi
}

/// The maximum growth in minimum-stack, across the whole zero-slope ladder, that
/// still counts as "no growth". Four bisection buckets over a ~4,000-step ladder
/// is under 4 bytes per step — far below any real per-level frame.
const ZERO_SLOPE_TOLERANCE: usize = 4 * RESOLUTION;

/// **The real bar, depth axis.** Two halves, and both are load-bearing:
///
/// 1. `name` survives a FIXED `stack` at depths 4, 16, 64, 256.
/// 2. Its bisected minimum stack at depth 4 and at depth 4,096 agree to within
///    [`ZERO_SLOPE_TOLERANCE`].
///
/// Half (1) alone is not sufficient — see the module header.
fn assert_depth_independent(name: &str, stack: usize) {
    for depth in [4usize, 16, 64, 256] {
        assert!(
            runs_within(stack, depth, name),
            "DEPTH-INDEPENDENCE GATE FAILED for `{}` at depth {} with a {} KiB stack.\n\
             This traversal's native stack grows with term nesting depth. The conversion\n\
             pattern is the explicit (node, Phase) worklist in `rhocalc_ast::lower_proc`\n\
             (Stage M-2) and `prattail/src/sppf_realize.rs`.",
            name,
            depth,
            stack / 1024
        );
    }
    assert_no_slope(name, 4, 4096, "depth");
}

/// **The real bar, width axis.** Same shape as [`assert_depth_independent`], with
/// the parameter meaning sibling count. The ladder runs further because
/// per-sibling costs are an order of magnitude below per-level costs.
fn assert_width_independent(name: &str, stack: usize) {
    for width in [4usize, 16, 64, 256] {
        assert!(
            runs_within(stack, width, name),
            "WIDTH-INDEPENDENCE GATE FAILED for `{}` at width {} with a {} KiB stack.\n\
             This traversal's native stack grows with SIBLING COUNT.",
            name,
            width,
            stack / 1024
        );
    }
    assert_no_slope(name, 4, 65536, "width");
}

/// The zero-slope half: minimum stack must not grow across a ~1,000× parameter
/// range. Profile-independent — it compares a traversal against ITSELF.
fn assert_no_slope(name: &str, lo_param: usize, hi_param: usize, axis: &str) {
    let lo = min_stack_for(name, lo_param);
    let hi = min_stack_for(name, hi_param);
    let growth = hi.saturating_sub(lo);
    assert!(
        growth <= ZERO_SLOPE_TOLERANCE,
        "ZERO-SLOPE GATE FAILED for `{}` on the {} axis: minimum stack grew {} KiB \
         between {} = {} ({} KiB) and {} = {} ({} KiB), which is {} B per step.\n\
         A converted traversal's native stack must not depend on {}.",
        name,
        axis,
        growth / 1024,
        axis,
        lo_param,
        lo / 1024,
        axis,
        hi_param,
        hi / 1024,
        growth / (hi_param - lo_param),
        axis
    );
    println!(
        "  {name} ({axis}): O(1) — {} KiB at {lo_param}, {} KiB at {hi_param}",
        lo / 1024,
        hi / 1024
    );
}

/// **Tripwire for traversals not yet converted.** Bisects the minimum stack at
/// two parameters, derives bytes-per-step, and fails if it exceeds `ceiling`.
///
/// This deliberately does NOT claim the traversal is fixed. It claims only that
/// it has not got worse. Every caller documents why its subject is still here.
fn assert_slope_below(name: &str, ceiling_bytes_per_step: usize, lo: usize, hi_param: usize) {
    let s_lo = min_stack_for(name, lo);
    let s_hi = min_stack_for(name, hi_param);
    let per_step = s_hi.saturating_sub(s_lo) / (hi_param - lo);

    assert!(
        per_step <= ceiling_bytes_per_step,
        "Θ(DEPTH) TRIPWIRE for `{}`: {} B/step exceeds the {} B/step ceiling \
         ({} KiB @ {} -> {} KiB @ {}).\n\
         Either a traversal regressed, or codegen changed materially.",
        name,
        per_step,
        ceiling_bytes_per_step,
        s_lo / 1024,
        lo,
        s_hi / 1024,
        hi_param
    );
    println!("  {name}: {per_step} B/step (ceiling {ceiling_bytes_per_step})");
}

/// Per-profile ceiling. Debug frames are several times release because `-O0` does
/// not overlay `match`-arm stack slots; see the module header.
fn ceiling(debug: usize, release: usize) -> usize {
    if cfg!(debug_assertions) {
        debug
    } else {
        release
    }
}

// ---------------------------------------------------------------------------
// THE GATE
// ---------------------------------------------------------------------------

/// Lowering traversals converted to a heap-bounded (explicit worklist) form.
/// Membership of these lists is the deliverable; they only ever grow.
///
/// ⚠ **The depth list is EMPTY at present, and that is a deliberate, honest state
/// rather than an oversight.** M-1 split all 89 arms of `lower_proc` into
/// per-arm `#[inline(never)]` frames and took the measured cost from 48,392 to
/// 15,132 B/level — a 3.20× constant-factor win that moved the main-thread ceiling
/// from depth 169 to 542. It did **not** change the CLASS: the traversal is still
/// Θ(depth), so listing any lowering subject here would be a false claim. The
/// residual is pinned, with its number, by [`lowering_theta_depth_tripwire`].
///
/// M-2 is what empties the tripwire into this list: an explicit `(Job, Phase)`
/// worklist over the whole 19-member recursion SCC (`lower_proc` ⇄ `lower_list` /
/// `lower_name` / `lower_method` / `lower_binary_expr` / `lower_pfor_user` / …),
/// in the idiom of `prattail/src/sppf_realize.rs:164`.
///
/// ★ The WIDTH list is populated already, and it is a real result rather than a
/// consolation: `lower_list` iterates its elements instead of folding them
/// recursively, so sibling count never reached the host stack. That axis is
/// asserted, not assumed — a future arm that recursed on a list tail would turn
/// this test red without anyone having to think of it.
#[test]
fn lowering_is_depth_independent() {
    let converted_depth: &[&str] = &[
        // "lower_depth",   // M-2 — the CastList ⇄ lower_list cycle
        // "lower_add",     // M-2 — the binary-expr cycle
        // "lower_par",     // M-2 — the PParInfix cycle
    ];
    let converted_width: &[&str] = &["lower_width"];

    for name in converted_depth {
        // 1 MiB is well below what even the M-1 form needs at depth 256.
        assert_depth_independent(name, 1024 * 1024);
    }
    for name in converted_width {
        assert_width_independent(name, 1024 * 1024);
    }
    if converted_depth.is_empty() {
        println!(
            "no lowering traversal is depth-independent yet — M-1 is a constant-factor result; \
             see `lowering_theta_depth_tripwire` and docs/design/audits/lowering-stack-depth-audit-2026-07-27.md"
        );
    }
}

/// Tripwire over the lowering while it is still Θ(depth). Ceilings are ~1.5× the
/// values measured on 2026-07-27 (`docs/design/audits/lowering-stack-depth-audit-2026-07-27.md` §5), so ordinary
/// codegen drift will not flake while a real regression still trips.
///
/// A subject LEAVES this list only by moving to
/// [`lowering_is_depth_independent`], never by having its ceiling raised.
///
/// Measured 2026-07-27, debug, bytes per nesting level:
/// `lower_depth` 15,132 (was 48,392 before the M-1 arm split).
#[test]
fn lowering_theta_depth_tripwire() {
    assert_slope_below("lower_depth", ceiling(23_000, 6_000), 16, 128);
    assert_slope_below("lower_add", ceiling(23_000, 6_000), 16, 128);
    assert_slope_below("lower_par", ceiling(23_000, 6_000), 16, 128);
}

/// **M-6, WIDTH axis — the parser does not grow with sibling count.**
///
/// Measured 2026-07-27: 471,040 bytes at width 16, 32, 64, 128, 256, 1,024 AND
/// 4,096 — identical to the byte across a 256× range. Slope **0**.
///
/// ⚠ The ladder stops at 16,384 rather than 65,536 for a practical reason: parse
/// TIME is roughly linear in sibling count (measured 1.13 s at 1,024 and 20.2 s at
/// 16,384) and a bisection runs ~20 probes per rung. 4 → 16,384 is still a 4,096×
/// range, which no non-zero per-sibling frame could survive.
#[test]
fn parsing_is_width_independent() {
    assert_no_slope("parse_width", 4, 16384, "width");
}

/// **★ M-6, DEPTH axis — a CORRECTION, and the reason the ladder must be wide.**
///
/// This gate's first version asserted that the parser was depth-INDEPENDENT, on the
/// strength of a measurement that read 471,040 bytes at depth 16, 32, 64 and 128 —
/// identical to the byte at every rung. **That conclusion was wrong, and this gate
/// caught it**, which is worth more than the number it was wrong about.
///
/// The parser has a large fixed intercept — ~460 KiB of generated recognizer tables
/// and driver frame. (It is genuinely the parser's, not the harness's: the cheapest
/// subject in this binary, `lower_width`, bisects to 98,304 bytes.) Below depth
/// ≈ 256 the per-level cost is entirely **masked** by that intercept, so a ladder
/// confined to 16 → 128 reads a flat line and reports a slope of zero.
///
/// Widening the ladder resolves it:
///
/// | depth | min stack (B) | pairwise B/level |
/// |---|---|---|
/// | 128 | 471,040 | — |
/// | 256 | 499,712 | 224 |
/// | 512 | 815,104 | 1,232 |
/// | 1,024 | 1,536,000 | 1,408 |
/// | 2,048 | 2,977,792 | 1,408 |
/// | 4,096 | 5,861,376 | 1,408 |
///
/// The asymptote is **1,408 B/level**, stable to the byte across the last three
/// intervals. The parse path is therefore Θ(depth) after all — it was simply never
/// the binding constraint, at 10.7× cheaper than the M-1 lowering (15,132) and 34×
/// cheaper than the original (48,392).
///
/// ★ **The methodological lesson, which generalises past this subject.** The module
/// header warns that a large intercept with a small slope passes a FIXED-STACK
/// ladder while still being Θ(depth). This is that hazard's dual: a large intercept
/// with a small slope also reads as *zero slope* on a ladder that never leaves the
/// intercept-dominated regime. Both probe points of a slope measurement must sit
/// clear of the subject's own floor, or the derived slope is understated — here, to
/// zero. That is why the ceilings below are probed at 512 and 4,096 rather than at
/// the 16 and 128 that produced the retracted claim.
///
/// The shape of the growth (flat to ≈256, then linear) is reported as measured; the
/// mechanism behind the knee is not established here and is deliberately not
/// guessed at.
#[test]
fn parser_theta_depth_tripwire() {
    // ~1.5× the measured 1,408 B/level, per profile, as everywhere else in this file.
    assert_slope_below("parse_depth", ceiling(2_200, 900), 512, 4096);
}

/// The reported reproducer, end-to-end (parse **and** lower), at a depth far past
/// the one that faulted, on the stack the `rhocalc` binary's MAIN thread actually
/// gets (`ulimit -s` default, 8 MiB).
///
/// This is the statement of the bug in one assertion: `@"OUT"!([[…[1]…]])` at
/// depth 144 aborted the process before Stage M.
#[test]
fn reported_reproducer_survives_the_default_main_thread_stack() {
    const DEFAULT_MAIN_THREAD_STACK: usize = 8 * 1024 * 1024;
    // Depth 256 is ~1.9× past the depth at which the bug was reported (bisected: the
    // main thread failed first at 170, and the DEFAULT configuration failed at 133 —
    // on the tokio worker, see the ledger §2), and comfortably inside what the M-1
    // form supports (measured ceiling 542). It is deliberately NOT set near that
    // ceiling: this test states "the reported bug is fixed", and a value chosen to
    // sit one rung below the current limit would be re-measuring the limit instead.
    // When M-2 lands, `lower_depth` joins `lowering_is_depth_independent` and this
    // constant stops being interesting.
    assert!(
        runs_within(DEFAULT_MAIN_THREAD_STACK, 256, "reproducer"),
        "REGRESSION: `@\"OUT\"!([[…[1]…]])` at depth 256 no longer survives parse+lower on \
         an {} MiB stack — the reported SIGSEGV is back or worse.",
        DEFAULT_MAIN_THREAD_STACK / (1024 * 1024)
    );
}

/// Measurement driver: prints the bisected minimum stack for every subject at a
/// ladder of parameters, and the derived bytes-per-step. `#[ignore]`d because it
/// is an INSTRUMENT, not an assertion — the assertions above are the gate.
///
/// ```text
/// cargo test -p rholang-runtime --test stack_depth_gate -- --ignored --exact report_slopes --nocapture
/// ```
#[test]
#[ignore = "measurement instrument; run explicitly with --nocapture"]
fn report_slopes() {
    if std::env::var("GATE_SUBJECT").is_ok() {
        // A child invocation reached here through `--run-ignored all`; do nothing.
        return;
    }
    let subjects: &[(&str, &[usize])] = &[
        ("lower_depth", &[4, 16, 64, 256, 1024, 4096]),
        ("lower_add", &[4, 16, 64, 256, 1024, 4096]),
        ("lower_par", &[4, 16, 64, 256, 1024, 4096]),
        ("lower_width", &[4, 256, 4096, 65536]),
        ("parse_depth", &[4, 16, 64, 128]),
        ("parse_width", &[4, 16, 64, 128]),
        ("reproducer", &[4, 16, 64, 128]),
    ];
    println!("subject,param,min_stack_bytes");
    for (name, ladder) in subjects {
        let mut points: Vec<(usize, usize)> = Vec::with_capacity(ladder.len());
        for &p in *ladder {
            let s = min_stack_for(name, p);
            println!("{name},{p},{s}");
            points.push((p, s));
        }
        let (p0, s0) = points[0];
        let (p1, s1) = points[points.len() - 1];
        let slope = (s1 as f64 - s0 as f64) / (p1 as f64 - p0 as f64);
        println!("# {name}: {slope:.1} B/step over {p0}..{p1}");
    }
}
