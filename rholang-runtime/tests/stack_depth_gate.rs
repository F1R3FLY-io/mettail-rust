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
            let no_core = libc::rlimit { rlim_cur: 0, rlim_max: 0 };
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
    println!(
        "  {name} − {baseline}: O(1) — {} KiB at {lo_param}, {} KiB at {hi_param}",
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
    let converted_depth: &[&str] =
        &["lower_leak", "lower_depth", "lower_add", "lower_par", "lower_neg"];
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
/// `List::ListLit(Vec<Proc>)`, and somewhere across that alternation the worklist is abandoned.
///
/// ★★ **WHERE it is abandoned — a CORRECTION (2026-07-29).** This paragraph used to end *"and the
/// worklist does not follow the hop through `List`. So the generated teardown is iterative within
/// a type and recursive across types."*
///
/// **What was believed:** that the generated work stacks are typed per category, and that a
/// driver silently falls back to host recursion on any edge that leaves its own category — so
/// `Proc::CastList(Arc<List>)` would be walked recursively because `List` is not `Proc`.
///
/// **What is true:** the cross-category edge is followed correctly, and the escape is one level
/// FURTHER DOWN, at the collection-ELEMENT boundary. From
/// `target/generated/rholang/iterative_cmp.rs`:
///
/// ```text
/// :2174  (Proc::CastList(ref l0), Proc::CastList(ref r0)) => {
/// :2175      stack.push(CmpTask::CmpList(&**l0 as *const _, &**r0 as *const _));
/// :2176  }                                    ↑ the CATEGORY HOP — pushed onto the work stack,
///                                               exactly as a converted driver should
/// :11128 (List::ListLit(a), List::ListLit(b)) => {
/// :11129     if a != b {              ↑ `a`, `b` are `&Vec<Proc>`. `!=` is `Vec<Proc>: PartialEq`
/// :11130         return false;          → `Proc::eq` per element → the driver re-enters ITSELF
/// :11131     }                          by HOST RECURSION, with no access to `stack`.
/// ```
///
/// The `Ord` half is the same shape with `let ord = a.cmp(b);` (`:34250`), and the pattern
/// repeats verbatim in the other sloped drivers — `iterative_hash.rs:5512`
/// `std::hash::Hash::hash(v, state)` on the whole `Vec`, `debug.rs:11346`
/// `std::fmt::Debug::fmt(&val, f)`, `match_pattern.rs:8392`
/// `(List::ListLit(v1), List::ListLit(v2)) if v1 == v2`. So the defect's shape is
/// `Category → Vec<Elem> → Elem`: iterative all the way down to the collection, then a
/// **whole-value delegation** to a trait method that cannot see the work stack.
///
/// **The measurement that decided it**, and why the ladder alone could not: every `*_add` twin
/// (`Proc::Add(Arc<Proc>, Arc<Proc>)`) is flat at 0–1 B/level while every `nested_list` original
/// is sloped, in both profiles — which the refuted explanation predicts just as well as the true
/// one, because `nested_add` differs from `nested_list` in TWO ways at once: it crosses no
/// category boundary *and* it contains no collection. `display.rs` is what separates them. It
/// walks the identical `Proc::CastList`/`List::ListLit` shape, and at `:14827` it pushes one
/// `DisplayTask::DisplayProc` per element instead of delegating the `Vec` —
///
/// ```text
/// List::ListLit(v) => {
///     stack.push(DisplayTask::WriteString("]".to_string()));
///     for (i, item) in v.iter().enumerate().rev() {
///         stack.push(DisplayTask::DisplayProc(item as *const _, 0u8));
/// ```
///
/// — and `ast_display` measures **0 B/level in both profiles on that very ladder**. A category hop
/// with no collection escape is flat; a collection escape is not. That is the discriminating
/// pair, and it is why the rewrite's target is `display.rs`'s element loop rather than a
/// per-category work-stack union.
///
/// ★ Recorded as a correction rather than silently replaced: the refuted reading survived in three
/// places in the tree precisely because it *explained the numbers*, and the next reader is better
/// served by knowing which explanation the numbers do NOT distinguish.
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

// ---------------------------------------------------------------------------
// ★★ THE GENERATED DRIVERS — gate what is FLAT, and hold the SLOPED SET to its exact membership
//
// `macros/src/gen/` emits a family of per-category traversals over the AST. They were MEASURED
// (`ecbe352c`, `f8f71f4c`) and re-measured on this build, but until now only ONE of them was
// gated — `ast_drop`, by `residue_ast_drop_has_not_got_worse`. Nothing would have gone red if any
// of the others had regressed, including the two that are the rewrite's own reference model.
//
// The two gates below are deliberately asymmetric, and the asymmetry is the policy:
//
//   * what is FLAT is gated as flat, by the same `assert_depth_independent` the converted
//     lowering answers to. `ast_display` and `ast_clone` are not merely passing subjects — they
//     are the existence proof that this shape CAN be walked in O(1) stack, and if either
//     regressed silently the rewrite would lose its model.
//   * what is SLOPED gets NO CEILING. A ceiling records a defect as a budget, and `ast_display`
//     proves the budget is unnecessary. What the sloped set gets instead is an assertion on its
//     MEMBERSHIP: exactly these subjects slope, no more and no fewer.
// ---------------------------------------------------------------------------

/// **The FLAT generated drivers, gated as flat on BOTH ladders.**
///
/// | subject | ladder | debug | release |
/// |---|---|---|---:|---:|
/// | `ast_display` | alternating (`CastList`/`ListLit`) | 0 | 0 |
/// | `ast_display_add` | pure (`Add(Arc<Proc>, Arc<Proc>)`) | 0 | 1 |
/// | `ast_clone` | alternating | 1 | 0 |
/// | `ast_clone_add` | pure | 0 | 0 |
///
/// (Bisected 2026-07-29, 16 → 4,096. A reading of 0 or 1 B/level is one 4 KiB bucket over a
/// 4,080-step ladder — the instrument's floor. Several of these are NEGATIVE before clamping.)
///
/// ★ **Why BOTH ladders, when the pure one is flat for everything.** On the pure chain every
/// driver reads 0, so a pure-ladder pass says nothing about a driver in particular. The
/// alternating ladder is where the discrimination lives. The pure rung is kept anyway because it
/// is the control that makes the alternating rung's *0* meaningful — a subject flat on both is
/// flat; a subject flat only on the pure one has simply not been tested.
///
/// ★ **Why these two are the reference implementations.** They reach O(1) stack by two DIFFERENT
/// mechanisms, and the rewrite needs both facts:
///
///   * `ast_display` is a real work-stack driver that does the hard case right. Its
///     `List::ListLit` arm pushes one `DisplayTask::DisplayProc` per element
///     (`display.rs:14827`) where every sloped driver hands the whole `Vec` to a trait method.
///     It is the shape the rewrite should copy.
///   * `ast_clone` is O(1) by REPRESENTATION, not by a driver at all: `iterative_clone.rs` was
///     DELETED (`651499e2`) once the ARC refactor (`9c55d81d`) made recursive children
///     `Arc<Cat>`, so the derived `Clone` is a refcount bump per child that never descends. It is
///     the reminder that some of these traversals do not need converting so much as deleting.
///
/// ⚠ Both were WATCHED RED before being trusted, by perturbing the subject rather than the
/// assertion — see the campaign record. A gate nobody has seen fail is a gate nobody has tested.
#[test]
fn flat_generated_drivers_are_depth_independent() {
    // 1 MiB, the same bound the converted lowering is held to. Measured floors for these four:
    // 20–72 KiB debug, 20–28 KiB release.
    for name in ["ast_display", "ast_display_add", "ast_clone", "ast_clone_add"] {
        assert_depth_independent(name, 1024 * 1024);
    }
}

// ── the SLOPED SET, and its exact membership ────────────────────────────────

/// The stack every driver subject is offered for the flat/sloped classification.
const CLASSIFY_STACK: usize = 1024 * 1024;

/// The depth at which a slope becomes decisive at [`CLASSIFY_STACK`].
///
/// ★ Chosen by measurement, not by taste. The classification is a single fixed-stack question —
/// *does this subject survive 1 MiB at depth D?* — which is ~1,000× cheaper than bisecting (two
/// `exec`s per subject instead of ~40), and it is sound only if D clears the SHALLOWEST slope in
/// the set by a wide margin. That is `ast_drop` in release at 94 B/level, whose 1 MiB budget runs
/// out at ≈ 10,900 levels; 32,768 is 3× past it. Calibrated at D ∈ {8,192, 16,384, 32,768,
/// 65,536} in both profiles: every flat subject survives all four, every sloped one fails from
/// 16,384 (release) or 8,192 (debug) onward. There is no D in that range where the partition is
/// ambiguous, and 32,768 sits in the middle of the unambiguous region.
const CLASSIFY_DEPTH: usize = 32_768;

/// ⚠ The NON-VACUITY floor. A subject that cannot run at all fails the deep probe and would be
/// silently counted as "sloped"; every subject must therefore first be shown to survive
/// [`CLASSIFY_STACK`] at a trivial depth. A broken subject is a THIRD outcome and the gate says
/// so by name rather than absorbing it into the sloped set.
const CLASSIFY_FLOOR_DEPTH: usize = 16;

/// How a driver subject's depth behaviour is expected to read.
#[derive(PartialEq, Eq, Debug, Clone, Copy)]
enum Shape {
    /// Minimum stack does not grow with depth. The rewrite's target state for all of them.
    Flat,
    /// Θ(depth). ⚠ Recorded as a FACT, never as a budget — no ceiling accompanies it.
    Sloped,
    /// ★ Measured sloped, but the slope is **not this driver's**.
    ///
    /// The subject's own anti-vacuity assertion is `assert!(replaced != term)` /
    /// `assert!(normalized == term)`, and `!=`/`==` on `Proc` is `PartialEq` — `ast_eq`'s driver,
    /// re-entered on the same deep term. The named twin is the identical body with an EQ-FREE
    /// check, and it reads flat; the pair is what makes the confound a measurement rather than an
    /// argument.
    ///
    /// ⚠ Kept as a LIVE CONTROL rather than deleted. If `iterative_cmp` is ever converted, these
    /// rows go flat and this gate goes RED — which is correct: the confound will have dissolved
    /// and the row belongs in `Flat`. A deleted control would have made that silent.
    SlopedByItsOwnAssertion { eq_free_twin: &'static str },
}

/// **The declared partition**, and the gate's only hand-written content.
///
/// Every `ast_*` subject the probe dispatches must appear here — the probe's own table is read at
/// run time (see [`probe_driver_subjects`]) and an undeclared subject FAILS. So the universe is
/// derived and only the expectation is declared, which is the whole point: a tenth driver cannot
/// arrive unnoticed.
///
/// Bisected 2026-07-29 on this build, alternating ladder, 16 → 4,096, debug / release B/level:
///
/// | subject | debug | release | shape |
/// |---|---:|---:|---|
/// | `ast_cmp` | 10,591 | 336 | Sloped |
/// | `ast_debug` | 10,543 | 462 | Sloped |
/// | `ast_eq` | 6,142 | 173 | Sloped |
/// | `ast_match_pattern` | 6,138 | 175 | Sloped |
/// | `ast_semantic_hash` | 1,215 | 208 | Sloped |
/// | `ast_hash` | 1,216 | 207 | Sloped |
/// | `ast_drop` | 252 | 94 | Sloped |
/// | `ast_subst` | 6,132 | 174 | **SlopedByItsOwnAssertion** |
/// | `ast_normalize` | 6,145 | 173 | **SlopedByItsOwnAssertion** |
/// | `ast_subst_noassert` | **0** | **0** | Flat |
/// | `ast_normalize_noassert` | **0** | **0** | Flat |
/// | `ast_display` | 0 | 0 | Flat |
/// | `ast_clone` | 1 | 0 | Flat |
///
/// ★ **Read the top four rows together with the bottom four.** `ast_eq`, `ast_match_pattern`,
/// `ast_subst` and `ast_normalize` bisect to 6,142 / 6,138 / 6,132 / 6,145 — four "independent"
/// traversals agreeing to three significant figures, which does not happen by coincidence. In
/// release the deep ends are 720 / 724 / 720 / 720 KiB, identical to the KiB. They agree because
/// they are the SAME measurement: `ast_eq`'s. Two of the four reach it through their own
/// assertion (excised above, and both then read 0); `ast_match_pattern` reaches it from inside
/// its own body — `match_pattern.rs:8392` is `(List::ListLit(v1), List::ListLit(v2)) if v1 == v2`,
/// a whole-`Vec` `PartialEq` — so it stays `Sloped`, and converting `iterative_cmp` would fix it
/// for free.
///
/// ⚠ **`ast_term_depth` is a TENTH driver, and the only one on the PURE ladder that slopes.**
/// `macros/src/gen/term_ops/depth.rs` emits `term_depth` as bare host recursion —
/// `1 + f0.term_depth()`, `1 + coll.iter().map(|x| x.term_depth()).max()` — with no work stack to
/// escape from, so its `*_add` twin slopes where all nine others are flat. It has NO CALLER
/// anywhere in the workspace, which is why it is a latent trap rather than a live exposure, and
/// why it is measured here rather than treated as urgent.
const EXPECTED_DRIVER_SHAPE: &[(&str, Shape)] = &[
    // ── the alternating ladder: where the discrimination lives ──
    ("ast_cmp", Shape::Sloped),
    ("ast_debug", Shape::Sloped),
    ("ast_eq", Shape::Sloped),
    ("ast_match_pattern", Shape::Sloped),
    ("ast_hash", Shape::Sloped),
    ("ast_semantic_hash", Shape::Sloped),
    ("ast_drop", Shape::Sloped),
    ("ast_term_depth", Shape::Sloped),
    ("ast_subst", Shape::SlopedByItsOwnAssertion { eq_free_twin: "ast_subst_noassert" }),
    ("ast_normalize", Shape::SlopedByItsOwnAssertion { eq_free_twin: "ast_normalize_noassert" }),
    ("ast_subst_noassert", Shape::Flat),
    ("ast_normalize_noassert", Shape::Flat),
    ("ast_display", Shape::Flat),
    ("ast_clone", Shape::Flat),
    // ── the pure ladder: flat for everything that HAS a work stack, and that is the finding ──
    ("ast_cmp_add", Shape::Flat),
    ("ast_debug_add", Shape::Flat),
    ("ast_eq_add", Shape::Flat),
    ("ast_match_pattern_add", Shape::Flat),
    ("ast_hash_add", Shape::Flat),
    ("ast_semantic_hash_add", Shape::Flat),
    ("ast_drop_add", Shape::Flat),
    ("ast_subst_add", Shape::Flat),
    ("ast_normalize_add", Shape::Flat),
    ("ast_subst_noassert_add", Shape::Flat),
    ("ast_normalize_noassert_add", Shape::Flat),
    ("ast_display_add", Shape::Flat),
    ("ast_clone_add", Shape::Flat),
    // ⚠ The exception that proves the rule: no work stack, so no benefit from having no collection.
    ("ast_term_depth_add", Shape::Sloped),
];

/// ⚠ The non-vacuity floor on the DERIVED universe. If `list_subjects` ever returned nothing —
/// a renamed mode, a probe that failed to run, a redirect that swallowed stdout — every
/// assertion below would iterate an empty set and PASS. This is the count at the time of writing;
/// it may only grow, and it must never be silently reduced to match a shrunken enumeration.
const MIN_DRIVER_SUBJECTS: usize = 28;

/// The `ast_*` subjects the PROBE dispatches, read from the probe itself.
///
/// ★ This is the derivation. `stack_depth_probe`'s `SUBJECTS` table is the single source of truth
/// for which subjects exist, and `GATE_SUBJECT=list_subjects` prints it one name per line. A
/// parent that hand-mirrored the list could not fail on a subject it had never heard of — the new
/// subject would simply go unclassified, which is a vacuous pass and precisely the hole this
/// closes.
fn probe_driver_subjects() -> Vec<String> {
    let output = std::process::Command::new(PROBE)
        .env("GATE_SUBJECT", "list_subjects")
        .env_remove("RUST_MIN_STACK")
        .output()
        .expect("stack_depth_gate: could not run the probe's subject enumeration");
    assert!(
        output.status.success(),
        "stack_depth_gate: `GATE_SUBJECT=list_subjects` exited {:?}. The probe must support the \
         enumeration mode for the driver-set gate to derive its universe.",
        output.status.code()
    );
    let listing = String::from_utf8(output.stdout)
        .expect("stack_depth_gate: the probe's subject enumeration was not UTF-8");
    let subjects: Vec<String> = listing
        .lines()
        .map(str::trim)
        .filter(|line| line.starts_with("ast_"))
        .map(str::to_owned)
        .collect();
    assert!(
        subjects.len() >= MIN_DRIVER_SUBJECTS,
        "stack_depth_gate: the probe enumerated only {} `ast_*` subjects, below the floor of {}. \
         Either the enumeration broke (in which case every classification below would pass \
         vacuously) or subjects were REMOVED, which needs saying out loud.",
        subjects.len(),
        MIN_DRIVER_SUBJECTS
    );
    subjects
}

/// The measured shape of one subject: `Flat` or `Sloped`, by the fixed-stack discriminator.
///
/// ⚠ `SlopedByItsOwnAssertion` is never returned — it is not something a measurement can see. It
/// is an ATTRIBUTION, and the gate checks it by requiring the declared eq-free twin to measure
/// flat while the subject itself measures sloped.
fn measured_shape(name: &str) -> Shape {
    assert!(
        runs_within(CLASSIFY_STACK, CLASSIFY_FLOOR_DEPTH, name),
        "NON-VACUITY FLOOR FAILED for `{}`: it does not survive a {} KiB stack even at depth {}. \
         That is a BROKEN SUBJECT, not a sloped one — its anti-vacuity assertion may be failing, \
         or its fixture may no longer parse. Fix it rather than letting the classification below \
         read it as Θ(depth).",
        name,
        CLASSIFY_STACK / 1024,
        CLASSIFY_FLOOR_DEPTH
    );
    match runs_within(CLASSIFY_STACK, CLASSIFY_DEPTH, name) {
        true => Shape::Flat,
        false => Shape::Sloped,
    }
}

/// **★★ The sloped set is EXACTLY this, and no ceiling is attached to any of it.**
///
/// Three failures, each of which has already happened once in this campaign's history:
///
/// 1. **A driver leaves the set silently.** `ast_subst` and `ast_normalize` were on record at
///    ~6,140 B/level, third- and fourth-worst of the nine. Both are flat; the slope was their own
///    `PartialEq` anti-vacuity assertion. Two of the "worst" rows dissolved, and nothing would
///    have noticed.
/// 2. **A tenth driver appears.** The family was on record as NINE. `term_depth` is a tenth, is
///    compiled into every language, and is bare host recursion. It was found by accident while
///    looking for an eq-free anti-vacuity instrument for (1).
/// 3. **A subject silently stops measuring.** Guarded by [`CLASSIFY_FLOOR_DEPTH`], because a
///    subject whose fixture stops parsing fails the deep probe and reads as "sloped" — a defect
///    reported as a confirmation.
///
/// ⚠ **Why there is no `assert_slope_below` on the sloped rows, stated once so it is not
/// re-litigated.** A ceiling records a defect as a budget: it passes forever at 10,591 B/level and
/// says nothing about whether that number should exist. `ast_display` walks the identical shape at
/// 0 B/level, so the achievable figure is known and it is zero. A subject leaves this set by being
/// CONVERTED — by moving to [`flat_generated_drivers_are_depth_independent`] — never by having a
/// ceiling raised. That is the same rule `residue_par_drop_has_not_got_worse` states for the
/// lowering residue, and the prior agent declined to ceiling these deliberately.
///
/// ⚠ **This gate does not bisect**, and that is why it can afford to be exhaustive: two `exec`s
/// per subject rather than ~40. See [`CLASSIFY_DEPTH`] for the calibration that makes a single
/// fixed-stack point sound.
#[test]
fn the_sloped_driver_set_is_exactly_the_declared_one() {
    let enumerated = probe_driver_subjects();

    // (a) TOTALITY, in the derived direction: every subject the probe dispatches is declared.
    for name in &enumerated {
        assert!(
            EXPECTED_DRIVER_SHAPE.iter().any(|(declared, _)| declared == name),
            "UNDECLARED DRIVER SUBJECT `{name}`: the probe dispatches it, and \
             `EXPECTED_DRIVER_SHAPE` does not classify it.\n\
             A new generated traversal must be measured and declared Flat or Sloped, not left to \
             be silently unclassified — an unclassified subject is exactly how a TENTH driver \
             hides (see this test's note, failure mode 2)."
        );
    }

    // (b) TOTALITY, in the declared direction: no stale rows for subjects that no longer exist.
    for (declared, _) in EXPECTED_DRIVER_SHAPE {
        assert!(
            enumerated.iter().any(|name| name == declared),
            "STALE DECLARATION `{declared}`: it is classified here but the probe no longer \
             dispatches it. A removed subject must be removed from this table too, or the table \
             stops being a description of anything."
        );
    }

    // (c) The measured partition matches the declared one, subject by subject.
    for (declared, expected) in EXPECTED_DRIVER_SHAPE {
        let measured = measured_shape(declared);
        match expected {
            Shape::Flat => assert_eq!(
                measured,
                Shape::Flat,
                "REGRESSION: `{declared}` is declared FLAT and now needs more than {} KiB at \
                 depth {}. A driver that was O(1) in stack has acquired a per-level frame. If \
                 this is `ast_display` or `ast_clone`, the rewrite has lost its reference model.",
                CLASSIFY_STACK / 1024,
                CLASSIFY_DEPTH
            ),
            Shape::Sloped => assert_eq!(
                measured,
                Shape::Sloped,
                "`{declared}` is declared SLOPED and now survives {} KiB at depth {} — it appears \
                 to have been CONVERTED.\n\
                 That is good news and this gate is still the right thing to fail: move the row to \
                 `Shape::Flat` and add the subject to \
                 `flat_generated_drivers_are_depth_independent`, so the new state is asserted \
                 rather than merely no longer contradicted.",
                CLASSIFY_STACK / 1024,
                CLASSIFY_DEPTH
            ),
            Shape::SlopedByItsOwnAssertion { eq_free_twin } => {
                assert_eq!(
                    measured,
                    Shape::Sloped,
                    "`{declared}` is declared sloped-by-its-own-assertion but now reads FLAT. \
                     Either its `PartialEq` anti-vacuity check was replaced (in which case this \
                     row and `{eq_free_twin}` are now the same subject and one should go), or \
                     `iterative_cmp` was converted — in which case the confound has dissolved and \
                     the row belongs in `Shape::Flat`."
                );
                assert_eq!(
                    measured_shape(eq_free_twin),
                    Shape::Flat,
                    "THE ATTRIBUTION NO LONGER HOLDS: `{declared}` is declared sloped only \
                     because its anti-vacuity assertion re-enters `ast_eq`, and its eq-free twin \
                     `{eq_free_twin}` is supposed to demonstrate that by reading FLAT. The twin \
                     is now sloped too, so the slope is NOT the assertion's after all and the \
                     driver itself must be re-examined — start by finding what recurses in it."
                );
            },
        }
    }
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
