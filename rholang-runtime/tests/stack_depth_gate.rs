//! # The Θ(depth) regression gate for the Rholang **lowering**
//!
//! **The defect this gate exists for.** `rholang_ast::lower_proc` translates a
//! parsed Rholang `Proc` into a normalized `rhoapi::Par`. Before Stage M it did
//! so by *host recursion*: one native frame per nesting level of the term. A
//! 30-byte program — `@"OUT"!([[[[…[1]…]]]])` — therefore aborted the process,
//! because a stack overflow is a `SIGSEGV` delivered on the guard page, not a
//! catchable error.
//!
//! Located under `gdb` on 2026-07-27:
//!
//! ```text
//! Thread 1 "rholang" received signal SIGSEGV, Segmentation fault.
//! mettail_rholang_runtime::rholang_ast::lower_proc () at rholang-runtime/src/rholang_ast.rs:931
//! Backtrace stopped: Cannot access memory        ← the guard page
//! ```
//!
//! ## ★ Why `RUST_MIN_STACK` is INERT on this path, and why this gate does not use it
//!
//! `rholang-runtime/src/bin/rholang.rs` is `#[tokio::main] async fn main`, so
//! parsing and lowering run on the process's **main** thread. `RUST_MIN_STACK`
//! is read only by `std::thread`'s spawn path — it cannot resize a main thread,
//! whose size is fixed by `ulimit -s` before `main` is entered. A sweep of
//! `RUST_MIN_STACK` from 1 MiB to 32 MiB against the reproducer reported "ok" at
//! every value **because it was controlling nothing**.
//!
//! ★ **So the probe must not use a spawned thread either.** An earlier form of
//! this gate ran each subject on a `std::thread::Builder::stack_size` thread.
//! That is a precise instrument, but it measures a **proxy**: a spawned thread's
//! stack is one `mmap` with a guard page, while a main thread's is a kernel-grown
//! VMA bounded by `RLIMIT_STACK` — and it is the latter that production faults
//! on. Every probe here therefore forks
//! [`stack_depth_probe`](../../src/bin/stack_depth_probe.rs), a program whose
//! `main` runs the subject directly, with `RLIMIT_STACK` installed in the child
//! before `exec`. That is exactly what `ulimit -s` does in the shell harness of
//! the audit's Appendix A, driven from Rust so the ladder is reproducible.
//!
//! ⚠ The probe cannot be a `#[test]` in this file, for a mechanical reason:
//! **libtest runs every test on a spawned thread** (`run_test_inner` always calls
//! `thread::Builder::spawn`, falling back to the current thread only when the OS
//! refuses to create one). A `#[test]` body therefore *cannot* execute on a main
//! thread, whatever the parent sets. A plain `fn main` can.
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
//! CHILD process: the gate spawns `stack_depth_probe` with `GATE_SUBJECT` /
//! `GATE_DEPTH` set and reads the exit status. 0 = survived.
//!
//! ⚠ And `RLIMIT_CORE` is set to 0 in the same `pre_exec` hook. A core dump of
//! this binary is ~305 MB and a single bisection produces dozens of faults; a
//! run that filled the disk would look like a gate failure and would not be one.
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
//!   (`target/generated/rholang/iterative_drop.rs`). So `drop(term)` is O(1) in
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
#![cfg(feature = "rholang-runtime")]


// ---------------------------------------------------------------------------
// the probe mechanism
//
// The subjects themselves live in `src/bin/stack_depth_probe.rs`, because they
// must run on a MAIN thread and libtest cannot give them one (see the module
// header). This file owns the ladder, the bisection and the assertions.
// ---------------------------------------------------------------------------

/// The probe program, located by Cargo at compile time. `CARGO_BIN_EXE_<name>` is set for
/// integration tests of the package that declares the `[[bin]]`, so the parent and the child
/// are always the same build — no path arithmetic off `current_exe()`, which breaks under
/// `cargo nextest`'s archive layout.
const PROBE: &str = env!("CARGO_BIN_EXE_stack_depth_probe");

/// Run one probe point in a child process, under `RLIMIT_STACK = stack`. `true` iff it
/// survived.
///
/// ★ The bound is installed with `setrlimit` in the forked child **before `exec`** — the same
/// thing `ulimit -s` does in a shell — so it governs the child's MAIN thread, which is where
/// production's lowering runs. `RLIMIT_CORE` goes to 0 in the same hook: a bisection produces
/// dozens of `SIGSEGV`s and each core of this binary is ~305 MB.
fn runs_within(stack: usize, depth: usize, subject_name: &str) -> bool {
    use std::os::unix::process::CommandExt;

    let mut command = std::process::Command::new(PROBE);
    command
        .env("GATE_SUBJECT", subject_name)
        .env("GATE_DEPTH", depth.to_string())
        // ⚠ Explicitly cleared. It cannot reach a main thread (see the module header), and a
        // value inherited from the developer's environment would make the ladder depend on it.
        .env_remove("RUST_MIN_STACK")
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null());

    // SAFETY: `setrlimit` is async-signal-safe and this hook allocates nothing. It runs in the
    // forked child between `fork` and `exec`, which is the only window in which `RLIMIT_STACK`
    // can still govern the main thread the kernel is about to lay out.
    unsafe {
        command.pre_exec(move || {
            let stack_limit = libc::rlimit {
                rlim_cur: stack as libc::rlim_t,
                rlim_max: stack as libc::rlim_t,
            };
            if libc::setrlimit(libc::RLIMIT_STACK, &stack_limit) != 0 {
                return Err(std::io::Error::last_os_error());
            }
            let no_core = libc::rlimit {
                rlim_cur: 0,
                rlim_max: 0,
            };
            if libc::setrlimit(libc::RLIMIT_CORE, &no_core) != 0 {
                return Err(std::io::Error::last_os_error());
            }
            Ok(())
        });
    }

    match command.status() {
        Ok(status) => status.success(),
        // ⚠ At the bottom of the exponential probe the rlimit can be too small for the kernel
        // to lay out the child's stack at all, and `execve` fails rather than the child
        // faulting. That is still "did not survive at this bound", and treating it as one keeps
        // the bisection monotone. A MISSING probe binary is a different thing and must not be
        // silently read as a fault.
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => panic!(
            "stack_depth_gate: the probe binary is missing at {PROBE}. Build it with \
             `--features rholang-runtime`."
        ),
        Err(_) => false,
    }
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
             pattern is the explicit (node, Phase) worklist in `rholang_ast::lower_proc`\n\
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

/// **The bar for a subject whose ladder contains a Θ(depth) traversal it does not own.**
///
/// Bisects `name` and `baseline` at both ends and asserts that the DIFFERENCE does not grow.
/// `baseline` must be the same subject with the traversal under test removed, so the delta is
/// that traversal and nothing else.
///
/// ★ Why this exists rather than a ceiling. `lower_new`'s ladder is dominated by
/// `moniker::Scope::new`, which closes each `new` body over its binder by walking it — measured
/// **1,055 B/level in debug** by `new_build`, which builds the identical ladder and lowers
/// nothing. A plain zero-slope assertion on `lower_new` would fail for a reason the lowering
/// neither causes nor can fix; a plain ceiling would pass while saying nothing about the
/// lowering. Subtracting the baseline says exactly the intended thing: *the `PNew` arm adds no
/// per-level frame of its own.*
///
/// Measured 2026-07-27, debug: `lower_new` 618,496 @ 512 and 4,403,200 @ 4,096; `new_build`
/// 561,152 and 4,341,760. Delta 57,344 → 61,440, i.e. **1.1 B/level**. In release both are flat
/// (LLVM flattens the moniker walk), so the delta is 0.
fn assert_no_slope_over_baseline(name: &str, baseline: &str, lo_param: usize, hi_param: usize) {
    let lo = min_stack_for(name, lo_param).saturating_sub(min_stack_for(baseline, lo_param));
    let hi = min_stack_for(name, hi_param).saturating_sub(min_stack_for(baseline, hi_param));
    let growth = hi.saturating_sub(lo);
    assert!(
        growth <= ZERO_SLOPE_TOLERANCE,
        "BASELINE-RELATIVE ZERO-SLOPE GATE FAILED for `{name}` over `{baseline}`: the excess \
         above the baseline grew {} KiB between depth {lo_param} ({} KiB) and depth {hi_param} \
         ({} KiB). The baseline subtracts the traversal this subject does not own, so a growing \
         delta is the LOWERING growing.",
        growth / 1024,
        lo / 1024,
        hi / 1024
    );
    println!("  {name} − {baseline}: O(1) — {} KiB at {lo_param}, {} KiB at {hi_param}", lo / 1024, hi / 1024);
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
/// ★ **M-2 landed.** `rholang_ast::drive` replaced the whole 87-member recursion component —
/// `lower_proc` ⇄ `lower_list` / `lower_name` / `lower_method` / `lower_binary_expr` /
/// `lower_pfor_user` / `lower_body_lifting_folds` / `lower_pattern_proc` / `lower_formula_in_env`
/// and the 68 `lower_arm_*` frames M-1 created — with one explicit `Job`/`Kont` worklist, in the
/// idiom of `prattail/src/sppf_realize.rs:164`.
///
/// Each subject names the cycle it would catch if that cycle came back. Bisected 2026-07-27,
/// B/level, on the ladder this test asserts (16 → 4,096):
///
/// | subject | cycle | debug | release |
/// |---|---|---|---|
/// | `lower_leak` | the lowering ALONE — both teardowns removed | **0** | **1** |
/// | `lower_depth` | `CastList` ⇄ `lower_list` — the reported reproducer's own path | **1** | **0** |
/// | `lower_add` | the binary-expression cycle | **0** | **0** |
/// | `lower_par` | `PParInfix`, which recurses on BOTH operands | **1** | **0** |
/// | `lower_neg` | `Int::NegInt` ⇄ `lower_int_value` — Θ(depth) OUTSIDE the component | **0** | **1** |
/// | `lower_width` | sibling count, `lower_list`'s iteration | **1** | **0** |
///
/// (A reading of 0 or 1 B/level is one 4 KiB bisection bucket across a 4,080-step ladder — the
/// instrument's floor. Two of the readings are NEGATIVE before clamping, which is what a flat
/// subject looks like when address-space layout shifts by a bucket.)
///
/// ★ `lower_leak` is the load-bearing one, and it is why the others can be trusted. It builds the
/// identical term, lowers it, and `mem::forget`s both sides, so its ladder contains the
/// conversion and nothing else. Before it existed, `lower_depth` read **252 B/level** and the
/// obvious conclusion — "the conversion is incomplete" — was WRONG: `ast_drop`, which lowers
/// nothing at all, read **254**. The slope was the AST's own teardown. A subject that measures
/// two traversals measures neither.
#[test]
fn lowering_is_depth_independent() {
    let converted_depth: &[&str] = &[
        "lower_leak",
        "lower_depth",
        "lower_add",
        "lower_par",
        "lower_neg",
    ];
    let converted_width: &[&str] = &["lower_width"];

    for name in converted_depth {
        // 1 MiB is an order of magnitude above what a converted traversal needs at any depth
        // (measured floors: 74–107 KiB debug, 29–37 KiB release).
        assert_depth_independent(name, 1024 * 1024);
    }
    for name in converted_width {
        assert_width_independent(name, 1024 * 1024);
    }
    // The `PNew` arm, against the ladder's own builder — see `assert_no_slope_over_baseline`.
    assert_no_slope_over_baseline("lower_new", "new_build", 512, 4096);
}

/// ★ **THE RESIDUE — every Θ(depth) traversal M-2 does NOT fix, with its number and its owner.**
///
/// The whole `rholang` binary went from **7,277 to 2,567 B/level** on its main thread (release,
/// bisected `ulimit -s` at depths 100 and 400, `RUST_MIN_STACK` pinned so only the main thread
/// binds). The gate's own lowering subjects went to **0**. The 2,567 that remain are *four other
/// traversals*, and none of them is reachable by the pushdown transform this conversion applied:
///
/// | subject | traversal | owner | debug | release |
/// |---|---|---|---|---|
/// | `par_drop` | `drop_in_place::<Par>` — `prost`'s DERIVED recursive `Drop` | `models` (f1r3node) | 368 | 95 |
/// | `ast_drop` | the `language!` iterative `Drop`, across a CROSS-TYPE hop | `macros/src/gen/` | 271 | 96 |
/// | `render` | `observation::render_par_text` — decode + format, both recursive | this crate | 3,674 | 911 |
/// | `lower_formula` | `formula::is_statically_false` ⇄ `is_statically_true` | `languages/src/` | 4,097 | 978 |
///
/// ★ **Why the two `Drop`s are not this conversion's to fix, stated precisely.** A pushdown
/// transform rewrites a traversal *whose text you own* into a worklist. `drop_in_place::<Par>` has
/// no text: it is glue the compiler derives from the type, and the only ways to change it are to
/// change the type or to intercept it at the call site. That is the **derived-impl class** — a
/// different repair with a different shape (f1r3node's own `par_children::dismantle` is the
/// call-site interception, and every subject above uses it, which is why `par_drop` is the only
/// one still paying). `ast_drop` is the same class with a twist worth recording: the `language!`
/// macro DOES emit a pooled iterative `Drop`, and `lower_add` — a pure `Proc::Add(Arc<Proc>, …)`
/// chain — is flat under it. But `nested_list` alternates `Proc::CastList(Arc<List>)` with
/// `List::ListLit(Vec<Proc>)`, and the worklist does not follow the hop through `List`. So the
/// generated teardown is iterative *within* a type and recursive *across* types.
///
/// `lower_formula`'s slope is likewise not the formula compiler — that WAS converted, and
/// `Job::Formula`/`Kont::Formula*` drive it from the same work stack. It is the syntactic
/// static-falsity judgement `lower_proc`'s `Matches` arm consults before lowering, which is a
/// mutually recursive pair in another crate.
///
/// **"The lowering is fixed" and "`rholang` is depth-independent" are different claims, and M-2
/// only makes the first.** Each row above needs its own conversion and its own move into
/// [`lowering_is_depth_independent`]. A subject leaves this list by being converted, never by
/// having its ceiling raised.
///
/// Ceilings are ~1.5× the measured values, per profile, as everywhere else in this file.
///
/// ⚠ **One `#[test]` per row, and that is a harness constraint rather than taste.** Each
/// `assert_slope_below` bisects twice and each bisection is ~20 child processes at depth 4,096,
/// so all four in one test ran ~500 s and `cargo nextest` terminated it at its 300 s per-test
/// cap — a RED gate that measured nothing. Split, each test fits comfortably, and a failure
/// names the one residue that regressed instead of the group.
#[test]
fn residue_par_drop_has_not_got_worse() {
    assert_slope_below("par_drop", ceiling(600, 200), 512, 4096);
}

/// See [`residue_par_drop_has_not_got_worse`].
#[test]
fn residue_ast_drop_has_not_got_worse() {
    assert_slope_below("ast_drop", ceiling(450, 200), 512, 4096);
}

/// See [`residue_par_drop_has_not_got_worse`].
#[test]
fn residue_render_has_not_got_worse() {
    assert_slope_below("render", ceiling(5_500, 1_500), 512, 4096);
}

/// See [`residue_par_drop_has_not_got_worse`].
#[test]
fn residue_static_falsity_judgement_has_not_got_worse() {
    assert_slope_below("lower_formula", ceiling(6_500, 1_500), 512, 4096);
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
/// the one that faulted, on the stack the `rholang` binary's MAIN thread actually
/// gets (`ulimit -s` default, 8 MiB).
///
/// This is the statement of the bug in one assertion: `@"OUT"!([[…[1]…]])` at
/// depth 144 aborted the process before Stage M.
#[test]
fn reported_reproducer_survives_the_default_main_thread_stack() {
    const DEFAULT_MAIN_THREAD_STACK: usize = 8 * 1024 * 1024;
    // ★ Depth 4,096 — 24× past the depth at which the bug was reported (bisected: the main
    // thread failed first at 170, and the DEFAULT configuration failed at 133, on the tokio
    // worker; see the ledger §2). Before M-2 this constant read 256, chosen to sit well inside
    // the M-1 ceiling of 542.
    //
    // ⚠ It is 4,096 rather than something absurd because this subject still has the PARSER in
    // its path, and the parser is Θ(depth) at ~1,240 B/level debug (`parse_depth`, and see
    // `parser_theta_depth_tripwire`). Measured: 5,865,472 B at depth 4,096, comfortably inside
    // 8 MiB; the next rung would not be. The lowering's own contribution is 0 — that is what
    // `lower_depth` and `lower_leak` assert.
    assert!(
        runs_within(DEFAULT_MAIN_THREAD_STACK, 4096, "reproducer"),
        "REGRESSION: `@\"OUT\"!([[…[1]…]])` at depth 4,096 no longer survives parse+lower on \
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
    let subjects: &[(&str, &[usize])] = &[
        ("lower_depth", &[4, 16, 64, 256, 1024, 4096]),
        ("lower_add", &[4, 16, 64, 256, 1024, 4096]),
        ("lower_par", &[4, 16, 64, 256, 1024, 4096]),
        ("lower_neg", &[4, 16, 64, 256, 1024, 4096]),
        ("lower_formula", &[512, 4096]),
        ("lower_new", &[512, 4096]),
        ("new_build", &[512, 4096]),
        ("lower_leak", &[4, 16, 64, 256, 1024, 4096]),
        ("lower_width", &[4, 256, 4096, 65536]),
        ("parse_depth", &[4, 16, 64, 128]),
        ("parse_width", &[4, 16, 64, 128]),
        ("reproducer", &[4, 16, 64, 128]),
        // ★ THE RESIDUE — expected to have a slope; measured so it is a number.
        ("par_drop", &[512, 4096]),
        ("ast_drop", &[512, 4096]),
        ("render", &[512, 4096]),
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
