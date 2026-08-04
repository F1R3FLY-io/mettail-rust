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
//! ## No production slope ceilings remain
//!
//! Earlier revisions retained per-profile ceilings for known recursive residues.
//! Those rows are now converted: a production subject is accepted only by
//! [`assert_no_slope`] over a wide ladder. Debug and release may have different
//! fixed intercepts, but neither profile is allowed growth with input depth.
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
//! ## ⚠ Teardown is a DIFFERENT traversal
//!
//! Both the input and the output of a lowering are deeply nested trees, and a
//! *recursive* `Drop` on either would make every reading `max(lowering, drop)` —
//! keeping this gate red for a reason that has nothing to do with the lowering.
//! Both sides now use generated, explicit worklists, but they remain separate
//! measurements so a teardown regression cannot be misattributed to lowering:
//!
//! * **`Proc` (the input) is already safe.** The `language!` macro generates a
//!   hand-written *iterative* `Drop` for the whole AST family — a pooled
//!   `DropTask` worklist with a re-entrancy flag
//!   (`target/generated/rholang/iterative_drop.rs`). So `drop(term)` is O(1) in
//!   stack and needs nothing from this file. (It also means a `Proc` cannot be
//!   destructured by value at all — `E0509`, cannot move out of a type that
//!   implements `Drop` — so a hand-rolled teardown here is not merely redundant,
//!   it does not compile.)
//! * **`Par` (the output) is now safe too.** f1r3node's schema generator emits
//!   `Drop` and the other recursive trait implementations over one explicit PDA.
//!   Lowering-only subjects still use
//!   `models::rust::rholang::par_children::dismantle` to isolate the lowering,
//!   while `par_drop` independently gates the generated destructor itself.
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

/// Where the exponential probe starts. Also — and this is the whole of #187 — the thing
/// that fixes the smallest answer [`measure_min_stack`] can ever produce.
const PROBE_START: usize = 16 * 1024;

/// ★★ #187 — **THE INSTRUMENT FLOOR, and it is a property of the instrument rather than
/// of any subject.**
///
/// [`measure_min_stack`] starts its exponential probe at [`PROBE_START`] = 16,384 B. A
/// subject that survives that bound never enters the doubling loop, so the bisection runs
/// on `[PROBE_START/2, PROBE_START] = [8,192, 16,384]`, and at [`RESOLUTION`] = 4,096 it
/// terminates the first time `hi - lo <= 4,096`:
///
/// ```text
///   lo = 8,192   hi = 16,384        hi - lo = 8,192  > 4,096   ⇒  mid = 12,288
///   survives 12,288  ⇒  hi = 12,288, lo = 8,192      hi - lo = 4,096  ⇒  STOP, answer 12,288
/// ```
///
/// **So 12,288 B is the smallest number this function can return, for every subject, on
/// every build.** A subject whose true requirement is anywhere in `(0, 12,288]` reports
/// 12,288 — and, critically, so does a subject whose true requirement is 12,000. The
/// answer is not a measurement; it is the bisection's floor showing through.
///
/// ⚠ **Twelve identical readings are ONE floor, not twelve agreeing measurements.** A
/// reader takes twelve identical numbers as strong corroboration. Here it is the exact
/// opposite: it is the signature of an instrument that cannot resolve any of them.
///
/// ★ **This floor is confined to ABSOLUTE readings. It does NOT touch the 0 B/level SLOPE
/// conclusions**, and the reason is worth stating because it is what keeps
/// `flat_generated_drivers_are_depth_independent`'s twenty-six rows standing: if a subject
/// reads the floor at BOTH ends of the ladder then its requirement is bounded above by the
/// floor at both ends, so its growth is bounded above by zero. Flat between two clamped
/// points still establishes flatness. What the floor invalidates is (a) any absolute
/// figure quoted as a measurement and (b) any derivation that *divides by* a floored
/// value — which is why [`assert_no_slope_over_baseline`] refuses to compute rather than
/// compute quietly.
///
/// ## What the achievable floor actually is, MEASURED — and the mechanism is NOT the one
/// on record
///
/// The claim on file was that the floor is `PTHREAD_STACK_MIN`-bound (16,384 on glibc
/// x86-64, `getconf PTHREAD_STACK_MIN`), because `std::thread::Builder::stack_size` clamps
/// every smaller request up with `cmp::max(stack, min_stack_size(attr))`
/// (`library/std/src/sys/thread/unix.rs:74`, where `min_stack_size` is glibc's
/// `__pthread_get_minstack` = `PTHREAD_STACK_MIN` + TLS).
///
/// **That is true of a DIFFERENT gate.** `f1r3node-rust-mettail/rholang/tests/stack_depth_gate.rs`
/// bisects `GATE_STACK` and its child runs the subject on
/// `std::thread::Builder::new().stack_size(stack)`, so every bound it poses below 16,384 is
/// silently clamped to 16,384 and its 12,288 answers are `PTHREAD_STACK_MIN`-bound exactly
/// as recorded.
///
/// ⚠ **This gate's probe is not that instrument, so `PTHREAD_STACK_MIN` is inert here.**
/// [`runs_within`] installs `RLIMIT_STACK` with `setrlimit` in the forked child *before
/// `exec`*, and the subject runs on that child's MAIN thread — §1.1's whole reason for
/// existing. `RLIMIT_STACK` is not a pthread attribute and is not clamped. Measured on this
/// box, 2026-07-30, `ast_clone` at depth 4 under a plain `ulimit -s`:
///
/// | `RLIMIT_STACK` | outcome | what it means |
/// |---|---|---|
/// | ≤ 11 KiB | `execve` fails, `E2BIG` "argument list too long" | the question CANNOT BE POSED |
/// | 12 – 20 KiB | `SIGSEGV` (139) | the child ran and genuinely wants more |
/// | ≥ 24 KiB | exit 0 | survives |
///
/// So the real barrier is Linux's rule that a child's `argv` + `envp` block must fit inside
/// the new `RLIMIT_STACK`: below 3 pages the kernel refuses the `exec` outright. And
/// [`runs_within`] maps that refusal to `Err(_) => false` — **the same verdict it gives a
/// genuine overflow.** That indistinguishability is the actual defect: the instrument cannot
/// tell "this subject needs more" from "I cannot ask this question".
///
/// ⇒ The achievable floor is **12 KiB (3 pages)** here, and it is *environment-size*-bound,
/// not `PTHREAD_STACK_MIN`-bound. That is a materially weaker claim than "a platform
/// constant": a smaller `envp` could in principle lower it, so it is a *weak* tunable. It
/// coincides numerically with the algorithmic floor above, which is why lowering
/// [`PROBE_START`] would buy nothing on this platform.
/// ## ⚠★★ THE PREMISE THAT BROUGHT #187 HERE IS REFUTED FOR THIS GATE — MEASURED
///
/// The report was: *"twelve of the fifteen depth subjects read exactly 12 KiB at 4, 12 KiB
/// at 4,096 — that is ONE floor showing through, not twelve agreeing measurements."* The
/// reasoning is exactly right and the diagnosis is exactly right for the gate it came from.
/// It is **not** this gate's state. `report_slopes`'s fifteen subjects, bisected on this
/// build 2026-07-30:
///
/// ```text
///   lower_neg          61,440 B  ←  the SMALLEST reading in the file, 5.0× the floor
///   lower_par          69,632
///   lower_depth        73,728
///   lower_leak         73,728
///   lower_add          77,824
///   lower_width        77,824
///   par_drop          208,896 … 1,527,808
///   lower_formula     249,856 … 1,507,328
///   parse_depth       491,520      parse_width 491,520      reproducer 487,424
///   new_build         561,152 … 4,349,952
///   lower_new         598,016 … 4,382,720
///   ast_drop / render  (per `residue_*`)
/// ```
///
/// **Not one subject reads 12,288 B, at either end, on either axis.** The floor is REAL and
/// provable from the algorithm, and it is entirely LATENT here — one leaner build away, which
/// is why the instrument is fixed rather than the numbers. Recording the refutation rather
/// than quietly acting on the premise, because "twelve identical readings" was itself the
/// kind of transcribed claim this campaign keeps finding drifted.
///
/// ## ★ THE AUDIT of every absolute use, and its result — 2026-07-30
///
/// The floor invalidates absolute figures. So every absolute stack quantity in this file and
/// in `docs/design/audits/lowering-stack-depth-audit-2026-07-27.md` was enumerated
/// mechanically (byte / KiB / MiB quantities ≥ one page, EXCLUDING `B/level`, `B/step` and
/// `B/sibling`, which are slopes) and compared against 12,288 B:
///
/// | artifact | absolute quantities | at or below the floor |
/// |---|---:|---:|
/// | `rholang-runtime/tests/stack_depth_gate.rs` | 35 | 11 |
/// | `docs/design/audits/lowering-stack-depth-audit-2026-07-27.md` | 20 | 2 |
/// | **total** | **55** | **13** |
///
/// **All 13 are references to the floor and the resolution CONSTANTS themselves** — the
/// eleven in this doc block and its siblings, plus two mentions of the 4 KiB [`RESOLUTION`]
/// in the audit. **ZERO recorded MEASUREMENTS are at or below the floor.** The closest is
/// 24,576 B (2.0× the floor), and today's run puts the cheapest subject at 28,672 B (2.3×).
///
/// ⇒ **No figure in this repository needs restating.** What was missing was not a correction
/// but the instrument change below, so that a future floored reading announces itself instead
/// of arriving as `12288`.
///
/// ⚠ **`f1r3node-rust-mettail` IS the affected repository and is NOT changed here.** Its
/// `rholang/tests/stack_depth_gate.rs` has a byte-identical `min_stack_for` but a
/// `GATE_STACK` / `thread::Builder::stack_size` child, so its floor is genuinely
/// `PTHREAD_STACK_MIN`-bound and its 12,288 answers are the clamp. Its
/// `BUILD_DEPTH_INVENTORY` and `docs/design/stack-safety/stack-safety-report-2026-07-29.md`
/// are where the absolute-figure audit has to be repeated. Reported, not edited — a
/// different repository and a different owner.
const SMALLEST_POSEABLE_STACK: usize = 12 * 1024;

/// The result of a minimum-stack bisection — and the point of the type is that
/// [`MinStack::BelowResolution`] is not spellable as a number.
///
/// ★ #187: `min_stack_for` used to return `usize`, so a subject under the instrument floor
/// came back as `12288` and was indistinguishable from a subject genuinely measured at
/// 12,288 B. Making the two cases different *variants* is what stops a below-floor subject
/// masquerading as a 12 KiB subject; every caller now has to say what it does with the
/// unresolved case, and the two callers that would have DIVIDED by it refuse.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum MinStack {
    /// Bisected to [`RESOLUTION`]: the subject needs at most this, and more than
    /// `this - RESOLUTION`.
    Bytes(usize),
    /// The subject survived [`SMALLEST_POSEABLE_STACK`], the smallest bound the instrument
    /// can pose at all. Its true requirement is somewhere in `(0, SMALLEST_POSEABLE_STACK]`
    /// and this instrument cannot say where.
    BelowResolution,
}

impl std::fmt::Display for MinStack {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MinStack::Bytes(bytes) => write!(f, "{} KiB", bytes / 1024),
            // ⚠ Never renders as a number. That is the entire mechanism.
            MinStack::BelowResolution => {
                write!(f, "<{} KiB (BELOW THE INSTRUMENT FLOOR)", SMALLEST_POSEABLE_STACK / 1024)
            },
        }
    }
}

/// Smallest stack (to [`RESOLUTION`] granularity) on which `name` survives at `depth`.
/// Exponential probe, then bisect.
///
/// ★ #187: answers [`MinStack::BelowResolution`] rather than the floor value when the
/// subject survives [`SMALLEST_POSEABLE_STACK`]. See that constant for why the floor exists
/// and what it does and does not invalidate.
fn measure_min_stack(name: &str, depth: usize) -> MinStack {
    let mut hi = PROBE_START;
    while hi <= 512 * 1024 * 1024 && !runs_within(hi, depth, name) {
        hi *= 2;
    }
    assert!(
        hi <= 512 * 1024 * 1024,
        "`{}` needed more than 512 MiB at parameter {}",
        name,
        depth
    );
    // ★ The floor check, and it is a MEASUREMENT rather than an inference from
    // `hi == PROBE_START`. Asking the smallest poseable bound directly is what separates
    // "survives 16 KiB" (which could still need 13 KiB) from "survives 12 KiB" (which the
    // instrument cannot resolve further).
    if hi == PROBE_START && runs_within(SMALLEST_POSEABLE_STACK, depth, name) {
        return MinStack::BelowResolution;
    }
    let mut lo = hi / 2;
    while hi - lo > RESOLUTION {
        let mid = (lo + hi) / 2;
        if runs_within(mid, depth, name) {
            hi = mid;
        } else {
            lo = mid;
        }
    }
    MinStack::Bytes(hi)
}

/// The bisected minimum in BYTES, for a caller that genuinely needs an absolute number.
///
/// ⚠ It refuses rather than substituting the floor. `why` names what the number was going
/// to be used for, so the failure says which derivation became unsound rather than only
/// that one did.
fn min_stack_bytes(name: &str, depth: usize, why: &str) -> usize {
    match measure_min_stack(name, depth) {
        MinStack::Bytes(bytes) => bytes,
        MinStack::BelowResolution => panic!(
            "#187 INSTRUMENT FLOOR: `{name}` survives {} B at parameter {depth}, which is the \
             smallest `RLIMIT_STACK` this instrument can pose — below it `execve` fails with \
             `E2BIG` and `runs_within` cannot distinguish that from an overflow. So its \
             minimum stack is UNRESOLVED, and {why} would be computed from a floor value \
             rather than from a measurement.\n\
             Substituting {} B here is exactly the defect #187 names: twelve subjects reading \
             the same floor look like twelve agreeing measurements and are one instrument \
             limit. Either raise the ladder's parameters until this end clears the floor, or \
             state the conclusion as a BOUND (`≤ {} B`) instead of a value.",
            SMALLEST_POSEABLE_STACK, SMALLEST_POSEABLE_STACK, SMALLEST_POSEABLE_STACK
        ),
    }
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
///
/// ★★ #187 — **THE ONE CONCLUSION THE INSTRUMENT FLOOR DOES NOT INVALIDATE**, and the
/// reason is stated here because this is the assertion that carries twenty-six rows.
///
/// If both ends read [`MinStack::BelowResolution`] the subject's requirement is bounded
/// above by [`SMALLEST_POSEABLE_STACK`] at BOTH ends, so its growth is bounded above by
/// zero. **Flat between two clamped points still establishes flatness.** The floor
/// invalidates absolute figures and any derivation that DIVIDES by one; it does not
/// invalidate a difference that is provably ≤ 0.
///
/// A MIXED pair — one end resolved, one below the floor — is still sound in the direction
/// this gate cares about, and only in that direction: the below-floor end is `≤ floor`, so
/// the growth is at most `resolved − 0` if the floor is at the low end, and at most
/// `floor − resolved` (i.e. negative, hence 0) if it is at the high end. Both are computed
/// as bounds below rather than as values.
fn assert_no_slope(name: &str, lo_param: usize, hi_param: usize, axis: &str) {
    let lo = measure_min_stack(name, lo_param);
    let hi = measure_min_stack(name, hi_param);
    // The GREATEST growth consistent with the two readings. A below-floor reading is an
    // upper bound of `SMALLEST_POSEABLE_STACK` and a lower bound of 0, so the worst case
    // puts the floor at the low end and the ceiling at the high end.
    let growth = match (lo, hi) {
        // Both clamped: growth ≤ floor − 0 is not tight enough, but growth ≤ 0 IS, because
        // both are bounded by the SAME floor and the gate's question is whether the
        // requirement grows with the parameter. Two values in `(0, floor]` differ by less
        // than `floor`, which is under `ZERO_SLOPE_TOLERANCE` = 4·4,096 by construction.
        (MinStack::BelowResolution, MinStack::BelowResolution) => 0,
        (MinStack::BelowResolution, MinStack::Bytes(high)) => high.saturating_sub(0),
        (MinStack::Bytes(_), MinStack::BelowResolution) => 0,
        (MinStack::Bytes(low), MinStack::Bytes(high)) => high.saturating_sub(low),
    };
    assert!(
        growth <= ZERO_SLOPE_TOLERANCE,
        "ZERO-SLOPE GATE FAILED for `{name}` on the {axis} axis: minimum stack grew {} KiB \
         between {axis} = {lo_param} ({lo}) and {axis} = {hi_param} ({hi}), which is {} B per \
         step.\n\
         A converted traversal's native stack must not depend on {axis}.\n\
         ⚠ #187: a reading rendered `<{} KiB (BELOW THE INSTRUMENT FLOOR)` is NOT a \
         measurement of {} B — it is the smallest bound this instrument can pose. The growth \
         above is the WORST CASE consistent with the readings, not a value.",
        growth / 1024,
        growth / (hi_param - lo_param),
        SMALLEST_POSEABLE_STACK / 1024,
        SMALLEST_POSEABLE_STACK
    );
    println!("  {name} ({axis}): O(1) — {lo} at {lo_param}, {hi} at {hi_param}");
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
/// ⚠★ #187: this function SUBTRACTS two absolute readings, so it is one of the two
/// derivations the instrument floor invalidates outright. `saturating_sub` of two floored
/// values is 0 — a difference that would read as "the arm adds nothing" for a subject whose
/// excess was never resolved at all. All four readings therefore go through
/// [`min_stack_bytes`], which refuses rather than substituting the floor.
fn assert_no_slope_over_baseline(name: &str, baseline: &str, lo_param: usize, hi_param: usize) {
    let why = "the baseline-relative excess (a SUBTRACTION of two absolute readings)";
    let lo = min_stack_bytes(name, lo_param, why)
        .saturating_sub(min_stack_bytes(baseline, lo_param, why));
    let hi = min_stack_bytes(name, hi_param, why)
        .saturating_sub(min_stack_bytes(baseline, hi_param, why));
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
        "lower_formula",
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

/// ★ **THE FORMER RESIDUE — retained as a historical attribution, now closed.**
///
/// The whole `rholang` binary went from **7,277 to 2,567 B/level** on its main thread (release,
/// bisected `ulimit -s` at depths 100 and 400, `RUST_MIN_STACK` pinned so only the main thread
/// binds). Those are the historical pre-closure measurements. The gate's lowering subjects went
/// to **0**, and the table records the later disposition of the other traversals rather than
/// silently deleting their former slopes:
///
/// | subject | traversal | owner | debug | release |
/// |---|---|---|---|---|
/// | ~~`par_drop`~~ | ~~`drop_in_place::<Par>` — `prost`'s derived recursive `Drop`~~ — **CONVERTED by f1r3node's generated trait PDA**, now **0** | `models` (f1r3node) | ~~368~~ → **0** | ~~95~~ → **0** |
/// | ~~`ast_drop`~~ | ~~the `language!` iterative `Drop`~~ — **CONVERTED by #162**, now −1 / 0 | `macros/src/gen/` | ~~271~~ | ~~96~~ |
/// | ~~`render`~~ | ~~recursive observation decode + format~~ — **CONVERTED by the observation PDA** | `runtime` / `rholang-runtime` | ~~3,674~~ → **0** | ~~911~~ → **0** |
/// | ~~`lower_formula`~~ | ~~mutual `is_statically_false` ⇄ `is_statically_true` recursion~~ — **CONVERTED by the one-pass formula PDA** | `languages/src/` | ~~4,097~~ → **0** | ~~978~~ → **0** |
///
/// ★ **Why the two `Drop`s were a different repair class, stated precisely.** A pushdown
/// transform rewrites a traversal *whose text you own* into a worklist. `drop_in_place::<Par>` had
/// no hand-written text: it was compiler-derived glue. f1r3node therefore changed schema codegen
/// to emit the recursive trait implementations, including `Drop`, over an explicit PDA. Its
/// `par_children::dismantle` call-site interception remains useful for isolating other subjects,
/// but `par_drop` now gates the production destructor directly. `ast_drop` was the same class
/// with a twist worth recording: the `language!`
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
/// `lower_formula` was the same kind of cross-boundary residue: its formula compiler already used
/// `Job::Formula`/`Kont::Formula*`, but the syntactic static-falsity judgement consulted before
/// lowering was still a mutually recursive pair in another crate. It now runs one explicit
/// `Visit`/`Build` post-order PDA that computes static-false, static-true, and host verdicts
/// together. `runtime/tests/formula_pda_source_equivalence.rs` imports that exact production
/// source and checks it against the recursive oracle, `formula_pda_stack_gate.rs` measures zero
/// main-thread slope within its 4 KiB resolution from depth 512 to 4,096, and the Rocq
/// `FormulaPdaEquivalence` theorem proves the recursive/PDA equality for every constructor and
/// arbitrary-arity separation.
///
/// **"The lowering is fixed" and "`rholang` is depth-independent" are different claims.** The
/// observation, formula, parser, generated AST traits, and generated `Par` traits therefore
/// received their own conversions before moving into constant-stack gates. A subject leaves
/// this historical list only by being converted, never by having its ceiling raised.
///
/// Rebuilt against f1r3node `26876b65` on 2026-08-03, `par_drop` requires the same minimum
/// native stack at depths 512 and 4,096 (0 B/step). The wider 4 → 4,096 ladder below is the
/// permanent regression condition.
#[test]
fn par_drop_is_depth_independent() {
    assert_depth_independent("par_drop", 1024 * 1024);
}

// ★★ `residue_ast_drop_has_not_got_worse` IS GONE, and that is how a subject is
// supposed to leave this list.
//
// It asserted `ast_drop` stayed under 450 B/level (debug) / 200 (release) while
// measuring 252/94. #162 converted the driver — `iterative_drop`'s
// collection-literal arm now pushes one owned `DropTask` per element instead of
// leaving the payload to `Vec<Proc>`'s recursive `Drop` — and `ast_drop` reads
// −1/0. The row moved to `flat_generated_drivers_are_depth_independent`, which
// asserts the new state rather than merely not contradicting it.
//
// This file's own rule, stated for the lowering residue and applied here: "A
// subject leaves this list by being converted, never by having its ceiling
// raised."

// ---------------------------------------------------------------------------
// ★★ #174 — THE HASH-KEYED COLLECTION COST NOW HAS A NAME AND AN ADDRESS.
//
// The finding on file was: *"hash-keyed collection literals cost 11.0× a list literal, and
// the figure matches no driver measured in isolation."* Both halves needed correcting.
//
// ⚠ IT WAS NEVER A PARSE-PHASE COST. `list_pair_parse` / `map_pair_parse` /
// `set_pair_parse` — the rungs that exist precisely to separate the phases — read
// **0 / 1 / 0 B/level** (debug, 16 → 4,096) and **−1 / −1 / 1** (release). The whole
// residue is in the LOWER phase.
//
// ★ AND IT MATCHED NO DRIVER BECAUSE IT IS NOT A DRIVER. Following the ONE structural
// difference between an `EList` and an `EMap`/`ESet`, through the `models` crate:
//
//   `rholang_ast.rs:2460  new_emap_par`   → `models/src/rust/utils.rs:715  new_emap_expr`
//     → `ParMapTypeMapper::par_map_to_emap(ParMap::new(…))`
//     → `models/src/rust/par_map.rs:18    ParMap::new` → `SortedParMap::create_from_vec`
//     → `models/src/rust/sorted_par_map.rs:30`
//            `let map: HashMap<Par, Par> = vec.into_iter().collect();`
//     → `models/src/lib.rs:284           impl Hash for Par`  ← HAND-WRITTEN, HOST-RECURSIVE
//
//   `rholang_ast.rs:2424  new_elist_par`  → `models/src/rust/utils.rs:897  new_elist_expr`
//     → `EListBody(EList { ps: Vec<Par>, … })` — a plain vector. No hash, no sort, no `Ord`.
//
// `impl Hash for Par` is `self.sends.hash(state); … self.exprs.hash(state); …`, i.e.
// `Vec<Expr>` → `Expr` → nested `Par` → `Par::hash`, on the native stack, once per level.
// `impl PartialEq for Par` (`:265`) has the same shape and runs on collision. This is the
// SAME CLASS as `par_drop`: an impl in `models`, not a `macros/src/gen/` traversal, which is
// exactly why no MeTTaIL driver measured in isolation ever matched it.
//
// MEASURED on the discriminating window 512 → 4,096, where the parser's depth-independent
// ~483 KB floor no longer compresses the slope:
//
//   | subject            | what it runs                          | debug | release |
//   |--------------------|---------------------------------------|------:|--------:|
//   | `list_pair_lower`  | parse + lower, NO hash (the control)   |     0 |      −1 |
//   | `par_hash`         | `lower_depth` + `Hash for Par`, alone |   625 |     113 |
//   | `par_hashmap`      | the `HashMap<Par,Par>` collect        |   636 |     113 |
//   | `map_pair_lower`   | the original #174 rung                |   597 |     144 |
//   | `set_pair_lower`   | the #174 rung, plus the sort          |   572 |     144 |
//
// `lower_depth` — the same build-lower-dismantle pipeline with the hash removed — reads
// **1 B/level debug, 0 release**. Adding nothing but `Hash for Par` to it produces 625.
// Four subjects that share only that impl agree inside ±5.3% in debug.
//
// ⚠ THE 11.0× AND THE 10,491 B/level ARE BOTH STALE. Re-measured on this build,
// `map_pair_lower` reads **227 B/level on the ladder the old figure was taken on**
// (16 → 1,024) — a 46× reduction — and `list_pair_lower` reads 0 rather than 950. #162
// and #189 converted the drivers that were stacked on top of the hash; what is left is the
// hash alone. A ratio against a control that now reads zero is not a number.
//
// ★ LIVING DISPOSITION (2026-08-03): f1r3node's schema codegen now emits `Hash`, `Eq`,
// `Ord`, and the other recursive trait implementations over the same explicit PDA used for
// `Drop`. Rebuilt against f1r3node `26876b65`, both `par_hash` and `par_hashmap` require the
// same minimum native stack at depths 512 and 4,096: **0 B/step**. The historical attribution
// above remains useful because it identifies what was converted; it no longer authorizes a
// non-zero slope.
// ---------------------------------------------------------------------------

/// Generated `Hash for Par` must use constant native stack across term depth.
#[test]
fn par_hash_is_depth_independent() {
    assert_depth_independent("par_hash", 1024 * 1024);
}

/// The `HashMap<Par, Par>` collection path must remain constant-stack too.
///
/// Kept as a second row rather than folded into [`par_hash_is_depth_independent`] because the
/// pair preserves the original attribution. `par_hash` runs `Hash for Par` and nothing else;
/// `par_hashmap` runs the `HashMap<Par, Par>` collect that `SortedParMap::create_from_vec`
/// performs, which is that hash plus `Eq for Par` on collision. Requiring both to be flat catches
/// a regression in either generated trait path without relying on their former byte ceilings.
#[test]
fn par_hashmap_is_depth_independent() {
    assert_depth_independent("par_hashmap", 1024 * 1024);
}

/// Observation decoding, rendering, and their temporary-value teardown must use constant native
/// stack. The child deliberately removes `Par` and AST teardown from the subject; both have
/// separate probes and would otherwise contaminate this measurement.
#[test]
fn observation_rendering_is_depth_independent() {
    assert_depth_independent("render", 1024 * 1024);
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
/// ★★ **#162 landed (2026-07-30) and this list grew from four rows to twenty-two.**
/// Eight of the nine work-stack drivers were Θ(depth) at the COLLECTION-ELEMENT
/// boundary — iterative all the way down to a container of sub-terms, then a
/// whole-value delegation to `PartialEq`/`Ord`/`Hash`/`Debug`/`Drop` that cannot see
/// the work stack. `macros/src/gen/term_ops/collection_walk.rs` is the one shared
/// mechanism that replaced it with one task per ELEMENT.
///
/// Bisected on this build, alternating ladder (`CastList`/`ListLit`) 16 → 4,096,
/// B/level, BEFORE → AFTER in each profile:
///
/// | subject | debug before | debug after | release before | release after |
/// |---|---:|---:|---:|---:|
/// | `ast_cmp` | 10,590 | **0** | 336 | **0** |
/// | `ast_debug` | 10,542 | **0** | 462 | **0** |
/// | `ast_eq` | 6,144 | **−1** | 173 | **0** |
/// | `ast_match_pattern` | 6,136 | **0** | 175 | **0** |
/// | `ast_hash` | 1,214 | **−2** | 207 | **1** |
/// | `ast_semantic_hash` | 1,216 | **−1** | 208 | **−1** |
/// | `ast_drop` | 254 | **−1** | 94 | **0** |
/// | `ast_subst` | 6,132 | **1** | 174 | **1** |
/// | `ast_normalize` | 6,145 | **2** | 173 | **0** |
/// | `ast_display` | 0 | 0 | 0 | 1 |
/// | `ast_clone` | 1 | 0 | 0 | 1 |
///
/// (0, ±1 and ±2 are all the instrument's floor: one 4 KiB bisection bucket across a
/// 4,080-step ladder is under 2 B/step. Negative readings are flat subjects whose
/// address-space layout shifted by a bucket.)
///
/// ★ **`ast_match_pattern` and `ast_semantic_hash` were converted for FREE**, and the
/// mechanism is worth stating because it is the leverage this whole rewrite ran on:
/// `match_pattern.rs`'s escape is `(List::ListLit(v1), List::ListLit(v2)) if v1 == v2`
/// — a whole-`Vec` `PartialEq` — and `semantic_hash`'s was a structural
/// `std::hash::Hash`. Both bottom out in drivers that are now flat, so neither arm
/// needed touching for the SLOPE. (`semantic_hash` did need converting for a
/// different reason: #154's fix moved it onto a per-element `semantic_hash`
/// re-entry, which re-introduced the slope at 4,096 B/level until its own
/// `AbsorbUsize` landed.)
///
/// ★ **`ast_subst` and `ast_normalize` are here as a DELIBERATE reclassification.**
/// They were declared `SlopedByItsOwnAssertion` — measured sloped, but only because
/// their anti-vacuity check is `assert!(replaced != term)` and `!=` on `Proc` is
/// `ast_eq`'s driver re-entered on the same deep term. That attribution predicted
/// that converting `iterative_cmp` would make them read flat, and it did. See
/// [`Shape::FlatAndItsEqFreeTwinAgrees`] for the control in its new form.
///
/// ★ **Why BOTH ladders, when the pure one is flat for everything.** On the pure
/// `Add(Arc<Proc>, Arc<Proc>)` chain every work-stack driver reads 0, so a
/// pure-ladder pass says nothing about a driver in particular. The alternating
/// ladder is where the discrimination lives. The pure rung is kept anyway because it
/// is the control that makes the alternating rung's 0 meaningful — a subject flat on
/// both is flat; a subject flat only on the pure one has simply not been tested.
///
/// ★ **The two original reference implementations stay, and they are why the rewrite
/// had a target at all:**
///
///   * `ast_display` is a real work-stack driver that does the hard case right. Its
///     `List::ListLit` arm pushes one `DisplayTask::DisplayProc` per element
///     (`display.rs:14827`) where every sloped driver handed the whole `Vec` to a
///     trait method. It is the shape the rewrite copied, and
///     `collection_walk::for_each_subterm` is that shape generalised.
///   * `ast_clone` is O(1) by REPRESENTATION, not by a driver at all:
///     `iterative_clone.rs` was DELETED (`651499e2`) once the ARC refactor
///     (`9c55d81d`) made recursive children `Arc<Cat>`, so the derived `Clone` is a
///     refcount bump per child that never descends. It is the reminder that some of
///     these traversals do not need converting so much as deleting.
///
/// ⚠ A reading of 0 here is NOT evidence on its own that the conversion is correct —
/// only that it is heap-bounded. The conversion also has to leave `Hash`, `Ord`,
/// `Debug` and `semantic_hash` computing the same VALUES, and those are consensus-
/// visible (`Proc` is a hash key inside the AST; `semantic_fingerprint` feeds the
/// realize dedup). That half is gated separately, by
/// `languages/tests/generated_traversal_boundary_laws.rs` and
/// `languages/tests/semantic_fingerprint_binder_in_collection_literal.rs`, which
/// compare framed write-STREAMS rather than digests or lengths — a value-only change
/// in a fixed-width encoding is invisible to any size- or count-based check.
#[test]
fn flat_generated_drivers_are_depth_independent() {
    // 1 MiB, the same bound the converted lowering is held to. Measured floors after
    // #162: 24–229 KiB debug, 24–29 KiB release.
    //
    // ★★ **DERIVED from [`EXPECTED_DRIVER_SHAPE`], never hand-listed** — and the reason is
    // a measured defect, not a style preference.
    //
    // This loop used to be a literal array of twenty-six names maintained beside a table
    // that already knew the answer. `ast_try_eval` and `ast_try_eval_cast` were added to
    // the table and not to the array, so both were CLASSIFIED as flat while being held
    // only to `assert_depth_independent`'s absence — an 8× looser bar (≈32 vs ≈4 B/level)
    // — and neither printed a slope. A second copy of a derived set is a copy that drifts,
    // and this campaign's record is that EVERY such copy drifted. Completing the array
    // would have been the same non-repair a fourth time; the array is deleted instead.
    //
    // ⚠ The predicate is "the shape ASSERTS depth-independence", which is **not** the same
    // as `Shape::Flat`. [`Shape::FlatAndItsEqFreeTwinAgrees`] is a flat assertion carrying
    // an ADDITIONAL obligation, so matching on `Shape::Flat` alone would have silently
    // DROPPED `ast_subst` and `ast_normalize` — a narrowing disguised as a derivation.
    // Measured on this build: 30 `Flat` + 2 `FlatAndItsEqFreeTwinAgrees` = 32 subjects
    // checked, against the 26 the array named; the six it gains are `ast_try_eval`,
    // `ast_try_eval_cast`, `ast_subst_noassert`, `ast_normalize_noassert`,
    // `ast_subst_noassert_add` and `ast_normalize_noassert_add`. Nothing is lost.
    let mut checked: Vec<&'static str> = Vec::with_capacity(EXPECTED_DRIVER_SHAPE.len());
    for (name, shape) in EXPECTED_DRIVER_SHAPE {
        match shape {
            Shape::Flat | Shape::FlatAndItsEqFreeTwinAgrees { .. } => {
                assert_depth_independent(name, 1024 * 1024);
                checked.push(name);
            },
            // Recorded as a FACT, never as a budget — a sloped row must NOT be held to a
            // flat bar. `ast_recursion_control` is the classifier's non-vacuity anchor.
            Shape::Sloped => {},
        }
    }

    // ★ The non-vacuity floor, itself derived. If the table were emptied, truncated, or
    // its rows all reclassified `Sloped`, the loop above would pass by checking nothing —
    // exactly the failure `MIN_DRIVER_SUBJECTS` exists to prevent one level up.
    //
    // The message prints the COUNT and the MEMBERSHIP so a correction is DERIVED rather
    // than decremented, following the #189 precedent that derived the generated-traversal
    // exception set from the census rather than from arithmetic.
    let sloped = EXPECTED_DRIVER_SHAPE
        .iter()
        .filter(|(_, s)| matches!(s, Shape::Sloped))
        .count();
    let expected_flat = MIN_DRIVER_SUBJECTS - sloped;
    assert_eq!(
        checked.len(),
        expected_flat,
        "DERIVED FLAT SET CHANGED SIZE: `flat_generated_drivers_are_depth_independent` \
         checked {} subjects, but `EXPECTED_DRIVER_SHAPE` declares {} non-sloped rows \
         (MIN_DRIVER_SUBJECTS {} − {} sloped).\n\n\
         Checked: {:?}\n\n\
         If a driver was legitimately added or reclassified, move MIN_DRIVER_SUBJECTS with \
         it in the SAME commit — it is the floor on the derived universe, not a tally to \
         reconcile afterwards. If it was not, a row has been lost.",
        checked.len(),
        expected_flat,
        MIN_DRIVER_SUBJECTS,
        sloped,
        checked
    );
    assert!(
        sloped >= 1,
        "VACUOUS CLASSIFIER: `EXPECTED_DRIVER_SHAPE` declares no `Sloped` row, so \
         `measured_shape` would answer `Flat` for every subject even if `CLASSIFY_DEPTH` \
         were wrong, and this test would pass without discriminating anything. \
         `ast_recursion_control` is that anchor and is never to be converted."
    );
}

// ── the SLOPED SET, and its exact membership ────────────────────────────────

/// The stack every driver subject is offered for the flat/sloped classification.
const CLASSIFY_STACK: usize = 1024 * 1024;

/// The depth at which a slope becomes decisive at [`CLASSIFY_STACK`].
///
/// ★ Chosen by measurement, not by taste. The classification is a single fixed-stack question —
/// *does this subject survive 1 MiB at depth D?* — which is ~1,000× cheaper than bisecting (two
/// `exec`s per subject instead of ~40), and it is sound only if D clears the SHALLOWEST slope in
/// the set by a wide margin.
///
/// ⚠⚠ RE-DERIVED TWICE ON 2026-07-30, because #162 CONVERTED the subject this bound was
/// calibrated against — and then converted its replacement too.
///
/// The original anchor was `ast_drop` in release at 94 B/level, whose 1 MiB budget runs out at
/// ≈ 10,900 levels, putting D = 32,768 3× past it. `ast_drop` was converted; the shallowest
/// surviving slope became `ast_term_depth` at 207 (≈ 5,065 levels, 6× margin). Then
/// `ast_term_depth` was converted too, and **every `ast_*` subject in the family became flat.**
///
/// ★ That is a VACUITY HAZARD, not a victory: with no sloped subject anywhere,
/// [`measured_shape`] would return `Flat` for everything even if this constant were 4, and the
/// whole partition would pass while asserting nothing. The anchor is therefore no longer a
/// generated driver at all — it is `ast_recursion_control`, a deliberately host-recursive walk of
/// the same ladder, owned by `stack_depth_probe.rs` and never to be converted. See its row in
/// [`EXPECTED_DRIVER_SHAPE`].
///
/// The constant is unchanged. The original calibration (D ∈ {8,192, 16,384, 32,768, 65,536} in
/// both profiles: every flat subject survives all four, every sloped one fails from 16,384
/// release / 8,192 debug onward) holds a fortiori for a control that recurses at least as steeply
/// as the drivers it replaced. Recorded in full because a bound whose justification has been
/// converted away is a bound nobody can check.
const CLASSIFY_DEPTH: usize = 32_768;

/// ⚠ The NON-VACUITY floor. A subject that cannot run at all fails the deep probe and would be
/// silently counted as "sloped"; every subject must therefore first be shown to survive
/// [`CLASSIFY_STACK`] at a trivial depth. A broken subject is a THIRD outcome and the gate says
/// so by name rather than absorbing it into the sloped set.
const CLASSIFY_FLOOR_DEPTH: usize = 16;

/// How a driver subject's depth behaviour is expected to read.
#[derive(PartialEq, Eq, Debug, Clone, Copy)]
enum Shape {
    /// Minimum stack does not grow with depth. #162's target state, reached by
    /// nine of the ten.
    Flat,
    /// Θ(depth). ⚠ Recorded as a FACT, never as a budget — no ceiling accompanies it.
    Sloped,
    /// ★★ **THE POST-CONVERSION FORM OF A CONTROL WHOSE PREDICTION CAME TRUE.**
    ///
    /// This variant used to be `SlopedByItsOwnAssertion { eq_free_twin }`, and it
    /// asserted that `ast_subst`/`ast_normalize` STILL SLOPED while their eq-free
    /// twins read flat. The point was an ATTRIBUTION, not a measurement: both
    /// subjects bisected to ~6,140 B/level, agreeing with `ast_eq` and
    /// `ast_match_pattern` to three significant figures, because all four were the
    /// SAME measurement — `ast_eq`'s. Two of them reached it through their own
    /// anti-vacuity assertion (`assert!(replaced != term)`, and `!=` on `Proc` is
    /// `ast_eq`'s driver re-entered on the same deep term), and excising the
    /// assertion made both read 0.
    ///
    /// Its doc carried an explicit prediction: *"If `iterative_cmp` is ever
    /// converted, these rows go flat and this gate goes RED — which is correct: the
    /// confound will have dissolved and the row belongs in `Flat`."*
    ///
    /// #162 converted `iterative_cmp`. Measured on this build: `ast_subst` 6,132 → 1
    /// (debug) and 174 → 1 (release); `ast_normalize` 6,145 → 2 and 173 → 0. **The
    /// prediction was borne out to the letter**, which is the strongest thing that
    /// can be said for an attribution — it was falsifiable and it survived.
    ///
    /// ⚠ Updated rather than DELETED, deliberately. The pairing is still the only
    /// thing that distinguishes "this driver is flat" from "this driver's assertion
    /// stopped dominating its ladder", so it stays live in its new form: the subject
    /// AND its eq-free twin must both read flat, AND they must AGREE. Before the
    /// conversion their DISAGREEMENT was the finding; now their agreement is. A
    /// deleted control would have made the next re-entry silent.
    FlatAndItsEqFreeTwinAgrees { eq_free_twin: &'static str },
}

/// **The declared partition**, and the gate's only hand-written content.
///
/// Every `ast_*` subject the probe dispatches must appear here — the probe's own table is read at
/// run time (see [`probe_driver_subjects`]) and an undeclared subject FAILS. So the universe is
/// derived and only the expectation is declared, which is the whole point: a tenth driver cannot
/// arrive unnoticed.
///
/// ★★ **#162 (2026-07-30) inverted this table.** It used to declare eight sloped subjects and six
/// flat; the sloped set is now down to the single classifier anchor. Bisected on this build,
/// alternating ladder, 16 → 4,096, debug / release B/level — the full before/after is in
/// [`flat_generated_drivers_are_depth_independent`]'s table.
///
/// ⚠ **The membership counts are DELIBERATELY NOT SPELLED HERE.** A numeral in prose beside a
/// table that already computes it is a transcription, and every transcription in this campaign
/// drifted — this doc alone carried "twenty-seven flat" against thirty-two non-sloped rows.
/// [`flat_generated_drivers_are_depth_independent`] derives the flat set from this table and
/// prints the count and the membership when it disagrees with [`MIN_DRIVER_SUBJECTS`]; read the
/// failure message, not a sentence.
///
/// ⚠ **`term_depth` was a different KIND of defect, and it is now CONVERTED.** The other nine had
/// a work stack and escaped it at the collection-element boundary.
/// `macros/src/gen/term_ops/depth.rs` emitted `term_depth` as bare host recursion — `1 +
/// f0.term_depth()`, `1 + coll.iter().map(|x| x.term_depth()).max().unwrap_or(0)` — with **no work
/// stack to escape from**. The tell was its `*_add` twin: `ast_term_depth_add` sloped at 2,367
/// B/level on the pure `Add` chain where every one of the other nine read 0. It needed a
/// CONVERSION, not a boundary fix.
///
/// ★ **Superseded, annotated rather than overwritten** (the campaign's convention): the sentence
/// that stood here — *"it is the only row below that is not `Flat`"* — described the table before
/// the conversion landed. `ast_term_depth` is `Shape::Flat` below, and the only non-`Flat` row is
/// `ast_recursion_control`, which is the classifier's non-vacuity anchor and is never converted.
///
/// ⚠⚠ **A CORRECTION TO THE RECORD ON `term_depth`.** The note that stood here said it "has NO
/// CALLER anywhere in the workspace, which is why it is a latent trap rather than a live
/// exposure." **MEASURED FALSE (2026-07-30).** `target/generated/rholang/dovetail_report.rs` calls
/// it at **40 sites** — `__max_depth = __max_depth.max(value.term_depth())`, once per
/// `RholangTermInner` arm inside the Dovetail e-graph build — emitted by
/// `macros/src/gen/runtime/dovetail_report/typed_report.rs:1845/1933/2659/2677`. The earlier
/// reading missed them because a `grep` of the SOURCE tree finds only the emitter's `quote!`
/// fragments; the call sites exist only after expansion. So `term_depth` is LIVE, deleting it is
/// off the table, and it must be converted.
const EXPECTED_DRIVER_SHAPE: &[(&str, Shape)] = &[
    // ── the alternating ladder: where the discrimination lives ──
    ("ast_cmp", Shape::Flat),
    ("ast_debug", Shape::Flat),
    ("ast_eq", Shape::Flat),
    ("ast_match_pattern", Shape::Flat),
    ("ast_hash", Shape::Flat),
    ("ast_semantic_hash", Shape::Flat),
    ("ast_drop", Shape::Flat),
    // ★ Converted by #162. It had no work stack at all — see the note above, which records
    // the pre-conversion reading rather than deleting it.
    ("ast_term_depth", Shape::Flat),
    // ★★ #189 — the ELEVENTH driver, converted. It was host-recursive exactly as
    // `term_depth` was, and it had NO SUBJECT, which is why neither this gate's
    // present-but-undeclared direction nor its declared-but-absent direction could see it.
    // See `every_generated_traversal_has_a_probe_subject`.
    ("ast_is_ground", Shape::Flat),
    // ★★ #189 residual — the TWELFTH driver, `try_eval`, and a CORRECTION to the census row
    // that named it. That row said `Int` had a worklist and "the other 15 categories are plain
    // host recursion". The first half is right; the second is FALSE, and the emitter says why:
    // `macros/src/gen/native/eval.rs:1201` selects the worklist iff `!pda_reduce_arms
    // .is_empty()`, and `pda_reduce_arms` is filled only by the HOL branch (:590) — so a
    // category takes the recursive branch EXACTLY when it declares no HOL rule, and a category
    // with no HOL rule has no same-category child to recurse into.
    //
    // MEASURED over the artifact as well: a census of all 54 generated `eval.rs` files (62
    // `try_eval` impls) finds ZERO non-cast `try_eval()` call sites in any Rholang category.
    // What remains is the lossless CAST LATTICE, whose height (`BigRat ▸ BigInt ▸ Int ▸ UInt32
    // ▸ Bool`) bounds the host depth at five frames for a term of ANY depth.
    //
    // **Historical closure note.** The five-frame bound is Rholang-scoped, not a property of the
    // original emitter. A workspace census found 63 eager non-cast `try_eval()` sites and exposed
    // live Calculator and LedTest cross-category cycles. Commit `b0aa4e09` closed that generator
    // class with one typed pushdown machine per SCC of the post-auto-injection category graph.
    // `languages/tests/evaluator_cross_category_stack_safety.rs` now holds shallow recursive-oracle
    // equivalence, generated-shape refusal, and 20,000-edge small-stack regressions. This Rholang
    // row remains useful as its own grammar-specific gate; it is no longer evidence of an open
    // generator-wide residue.
    //
    // Two subjects rather than one, because a single ladder could not tell "the worklist is
    // flat" from "the lattice hop is per-edge": `ast_try_eval` drives the worklist down a
    // depth-N `NegInt` chain, `ast_try_eval_cast` puts an `Int ▸ BigRat` hop on top of the same
    // chain. See `stack_depth_probe::ast_try_eval_body`.
    ("ast_try_eval", Shape::Flat),
    ("ast_try_eval_cast", Shape::Flat),
    // ★ The retired confound, kept as a live control in its post-conversion form.
    (
        "ast_subst",
        Shape::FlatAndItsEqFreeTwinAgrees { eq_free_twin: "ast_subst_noassert" },
    ),
    // Environment substitution uses the same generated PDA but a distinct `SubstOp::EnvProc`
    // arm; keeping its own subject prevents the generated-file census from borrowing coverage
    // from the eager substitution path without exercising that arm.
    ("ast_env_subst", Shape::Flat),
    ("ast_parse_alt_filter", Shape::Flat),
    ("ast_var_inference", Shape::Flat),
    ("ast_language_var_collect", Shape::Flat),
    ("ast_flt_reflect", Shape::Flat),
    ("ast_dovetail_report", Shape::Flat),
    (
        "ast_normalize",
        Shape::FlatAndItsEqFreeTwinAgrees { eq_free_twin: "ast_normalize_noassert" },
    ),
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
    ("ast_term_depth_add", Shape::Flat),
    ("ast_is_ground_add", Shape::Flat),
    // ★★ THE CLASSIFIER'S OWN NON-VACUITY ANCHOR, and the only sloped row left.
    //
    // #162 converted all ten drivers, so with this row absent EVERY `ast_*` subject would be
    // flat — and `measured_shape` would then return `Flat` for everything even if
    // `CLASSIFY_DEPTH` were 4, making the whole partition pass vacuously. The constant was
    // calibrated against `ast_drop` at 94 B/level and then `ast_term_depth` at 207; both are
    // now converted, so the calibration lost its anchor.
    //
    // `ast_recursion_control` is a deliberately host-recursive walk of the same
    // `CastList`/`ListLit` ladder, owned by `stack_depth_probe.rs` and never to be converted.
    // It measures nothing about the generated drivers: it proves the CLASSIFIER can still tell
    // the two shapes apart. The depth-gate equivalent of `MIN_DRIVER_SUBJECTS`.
    ("ast_recursion_control", Shape::Sloped),
];

/// ⚠ The non-vacuity floor on the DERIVED universe. If `list_subjects` ever returned nothing —
/// a renamed mode, a probe that failed to run, a redirect that swallowed stdout — every
/// assertion below would iterate an empty set and PASS. This is the count at the time of writing;
/// it may only grow, and it must never be silently reduced to match a shrunken enumeration.
const MIN_DRIVER_SUBJECTS: usize = 39;

/// The `ast_*` subjects the PROBE dispatches, read from the probe itself.
///
/// ★ This is the derivation. `stack_depth_probe`'s `SUBJECTS` table is the single source of truth
/// for which subjects exist, and `GATE_SUBJECT=list_subjects` prints it one name per line. A
/// parent that hand-mirrored the list could not fail on a subject it had never heard of — the new
/// subject would simply go unclassified, which is a vacuous pass and precisely the hole this
/// closes.
fn probe_driver_subjects() -> Vec<String> {
    let subjects: Vec<String> = probe_subjects()
        .into_iter()
        .filter(|line| line.starts_with("ast_"))
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

/// EVERY subject the probe dispatches, unfiltered — the raw `SUBJECTS` enumeration.
///
/// ★ Split out from [`probe_driver_subjects`] for #189's census, which has to resolve
/// subject names that are NOT `ast_*` (`parse_depth` covers the recognizer). Filtering
/// before resolving would have made the recognizer's coverage claim unverifiable, which is
/// the same shape of hole #189 was.
fn probe_subjects() -> Vec<String> {
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
    listing
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .map(str::to_owned)
        .collect()
}

/// The measured shape of one subject: `Flat` or `Sloped`, by the fixed-stack discriminator.
///
/// ⚠ `FlatAndItsEqFreeTwinAgrees` is never returned — it is not something a single measurement can
/// see. It is an ATTRIBUTION over a PAIR, and the gate checks it by requiring the subject and its
/// declared eq-free twin to measure flat AND to agree.
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
/// ⚠ **Why there is no slope ceiling on the sloped row, stated once so it is not
/// re-litigated.** A ceiling records a defect as a budget and says nothing about whether that
/// number should exist. Every production driver is flat. The sole sloped row is the deliberately
/// recursive classifier control; it measures the instrument, not generated production code.
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
            EXPECTED_DRIVER_SHAPE
                .iter()
                .any(|(declared, _)| declared == name),
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
            Shape::FlatAndItsEqFreeTwinAgrees { eq_free_twin } => {
                let twin = measured_shape(eq_free_twin);
                assert_eq!(
                    measured,
                    Shape::Flat,
                    "`{declared}` is declared FLAT-with-an-eq-free-twin and now needs more than \
                     {} KiB at depth {}.\n\
                     Before #162 this row was `SlopedByItsOwnAssertion`: it measured sloped, but \
                     only because its anti-vacuity assertion (`assert!(replaced != term)`) \
                     re-entered `ast_eq`'s driver on the same deep term. Converting \
                     `iterative_cmp` made it flat, exactly as that attribution predicted. If it \
                     is sloped again, either `iterative_cmp` regressed — check `{eq_free_twin}`, \
                     which shares this subject's body but NOT its assertion — or the driver \
                     itself acquired a per-level frame.",
                    CLASSIFY_STACK / 1024,
                    CLASSIFY_DEPTH
                );
                assert_eq!(
                    twin,
                    Shape::Flat,
                    "the eq-free twin `{eq_free_twin}` is sloped while `{declared}` is not. The \
                     twin is the SAME body with the `PartialEq` anti-vacuity check removed, so it \
                     cannot be the slopier of the two. Something is wrong with the twin subject \
                     itself."
                );
                assert_eq!(
                    measured, twin,
                    "`{declared}` and its eq-free twin `{eq_free_twin}` DISAGREE about their \
                     shape. Their agreement is what this control now asserts: before #162 the \
                     pair's disagreement proved the slope belonged to the assertion rather than \
                     to the driver, and after #162 their agreement proves the assertion no \
                     longer dominates the ladder. A disagreement in either direction means one \
                     of the two subjects is measuring something the other is not."
                );
            },
        }
    }
}

// ---------------------------------------------------------------------------
// ★★ #189 — THE TRAVERSAL CENSUS, derived from the GENERATED TREE
//
// ⚠ THE HOLE THIS CLOSES, stated first because it is the whole point.
//
// `the_sloped_driver_set_is_exactly_the_declared_one` totals in BOTH directions —
// present-but-undeclared and declared-but-absent both fail — over a universe it
// ENUMERATES from `stack_depth_probe`'s `SUBJECTS` table at run time rather than
// hand-mirroring it. That is a strong instrument, and it was completely blind to
// `is_ground`: **a driver with no probe subject is not a row in the table to be
// totalled.** A bidirectional totality gate over a universe that does not contain the
// defect cannot see the defect. That is exactly how the TENTH driver (`term_depth`)
// hid, and then this ELEVENTH one.
//
// So this gate derives its universe from the one artifact that actually grows when a
// new generated traversal is added: **the set of files the macro writes into
// `target/generated/rholang/`**. Every file gets a row saying what it is and how it is
// covered; a new emitter cannot land without one. Two derived floors keep the rows
// honest in the two ways a declaration can lie:
//
//   * a row claiming NOT-A-TRAVERSAL must describe a file with no self-recursive call
//     and no work-stack — so a traversal smuggled into an existing "inert" file fails;
//   * a row claiming a TRAVERSAL must name an entry point that is still present in the
//     file — so a row cannot go on describing something that has been deleted.
//
// ★ The measured answer to "how many generated traversals have NO probe subject" was
// **EIGHT** when #189 derived it, of which `is_ground` was one. #189's residual took a
// second — `eval.rs` — and the correction is worth stating, because the row was not
// merely stale, it was WRONG ABOUT THE MECHANISM: it reported fifteen categories as
// "plain host recursion" from a count of `try_eval` impls WITHOUT a worklist, and the
// emitter's own branch condition says a category takes that branch exactly when it has
// no HOL rule and therefore no same-category child to recurse into. Counting the impls
// that lack a work stack is not the same question as counting the impls that recurse.
//
// Every former residual now has a non-vacuous probe subject. There is deliberately no
// "unmeasured traversal" census state: adding a depth traversal without a subject is invalid.
// ---------------------------------------------------------------------------

/// How a generated file's recursion is accounted for.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Coverage {
    /// A probe subject exercises it, and `EXPECTED_DRIVER_SHAPE` classifies the subject.
    Subject(&'static str),
    /// It recurses, but not over the depth of an existing host term — so a depth ladder
    /// is not the instrument for it. The string says why.
    NotADepthTraversal(&'static str),
    /// It contains no self-recursive call and no work-stack at all. Asserted, not
    /// asserted-of.
    Inert,
}

/// ★ Every file `language!` writes for Rholang, with what it is and how its recursion is
/// accounted for. The FILE LIST is derived at run time; this table is the expectation.
const GENERATED_FILE_CENSUS: &[(&str, &str, Coverage)] = &[
    // ── the per-category AST drivers, every one of them measured ────────────────────
    //
    // ⚠ No count is spelled here. This header read "the ELEVEN per-category AST drivers,
    // ten already measured" while the block held TWELVE — it was written when `is_ground`
    // was the newest arrival and was not touched when `eval.rs`/`try_eval` joined. The
    // membership is the rows below; `every_generated_traversal_has_a_probe_subject` is
    // what enforces that each has a subject, and its failure message prints the set.
    ("iterative_cmp.rs", "cmp", Coverage::Subject("ast_cmp")),
    ("iterative_hash.rs", "hash", Coverage::Subject("ast_hash")),
    ("iterative_drop.rs", "drop", Coverage::Subject("ast_drop")),
    ("semantic_hash.rs", "semantic_hash", Coverage::Subject("ast_semantic_hash")),
    ("debug.rs", "fmt", Coverage::Subject("ast_debug")),
    ("display.rs", "fmt", Coverage::Subject("ast_display")),
    ("subst.rs", "subst", Coverage::Subject("ast_subst")),
    ("normalize.rs", "normalize", Coverage::Subject("ast_normalize")),
    ("match_pattern.rs", "match_pattern", Coverage::Subject("ast_match_pattern")),
    ("term_depth.rs", "depth_iterative", Coverage::Subject("ast_term_depth")),
    // ★★ #189 — the eleventh, converted and now measured.
    ("is_ground.rs", "ground_iterative", Coverage::Subject("ast_is_ground")),
    // ★★ #189 residual, RESOLVED — and the row it replaces was wrong about the mechanism.
    //
    // It read: "PARTIALLY converted: `Int` has an `__EvalFrame` worklist, the other 15
    // categories are plain host recursion". MEASURED FALSE. The emitter (`native/eval.rs:1201`)
    // takes the recursive branch exactly when a category declares no HOL rule, and such a
    // category has no same-category child to recurse into — its arms are the literal, the Var,
    // the auto-injected CASTS and `_ => None`. Rholang declares ONE HOL rule over a native
    // category (`NegInt`, `languages/src/rholang.rs:1257`), so `Int` alone needs a worklist and
    // the other fifteen have nothing to convert.
    //
    // The residue is the CAST LATTICE, and it is a bound rather than an absence: at most five
    // host frames (`BigRat ▸ BigInt ▸ Int ▸ UInt32 ▸ Bool`) for a term of any depth. Both
    // subjects measure it — see `EXPECTED_DRIVER_SHAPE`'s note.
    //
    // **RHOLANG-SCOPED.** This row is correct for this Rholang gate, but it was never a
    // generator-wide proof. The former Calculator/LedTest cyclic residue is now closed by the
    // SCC pushdown machines at `b0aa4e09`; its independent oracle and deep small-stack gates live
    // in `languages/tests/evaluator_cross_category_stack_safety.rs`.
    ("eval.rs", "try_eval", Coverage::Subject("ast_try_eval")),
    // ── the RECOGNIZER: a traversal of the INPUT, measured on both axes ─────────────
    ("parser.rs", "parse", Coverage::Subject("parse_depth")),
    ("wpda.rs", "semantic_fingerprint", Coverage::Subject("parse_depth")),
    // ── ⚠ Originally six host-recursive walks with no subject; one remains. ───────────
    //
    // Each is a per-category descent over an existing term (or, for `dovetail_report`,
    // over a derivation whose depth IS the term's) emitted as bare host recursion, with
    // nothing in this file measuring it. Reported by #189's census rather than fixed:
    // #189's scope is `is_ground`, and a conversion needs its own subject, its own
    // anti-vacuity fixture and its own RED before green.
    ("env_subst.rs", "subst_by_name_proc", Coverage::Subject("ast_env_subst")),
    (
        "parse_alt_filter.rs",
        "uniform_flags_iterative",
        Coverage::Subject("ast_parse_alt_filter"),
    ),
    (
        "var_inference.rs",
        "infer_var_type_iterative",
        Coverage::Subject("ast_var_inference"),
    ),
    (
        "language_struct.rs",
        "collect_all_proc_vars",
        Coverage::Subject("ast_language_var_collect"),
    ),
    (
        "flt_reflect.rs",
        "__mettail_rho_net_reflect_proc",
        Coverage::Subject("ast_flt_reflect"),
    ),
    (
        "dovetail_report.rs",
        "__mettail_dovetail_build_proc_d",
        Coverage::Subject("ast_dovetail_report"),
    ),
    // ── recursion that is NOT over an existing term's depth ─────────────────────────
    (
        "rho_net_invocation.rs",
        "__mettail_rho_net_reflect_proc",
        Coverage::Subject("ast_flt_reflect"),
    ),
    (
        "random_generation.rs",
        "generate_random_at_depth_internal",
        Coverage::NotADepthTraversal(
            "a GENERATOR: recursion bounded by an explicit `max_depth` budget it decrements, \
             not by the depth of a term it was handed",
        ),
    ),
    (
        "term_generation.rs",
        "generate_all",
        Coverage::NotADepthTraversal("a GENERATOR, bounded by its own depth budget"),
    ),
    (
        "strategies.rs",
        "arb_proc",
        Coverage::NotADepthTraversal("proptest strategies: generators, bounded by `max_depth`"),
    ),
    (
        "tests_prop.rs",
        "proptest",
        Coverage::NotADepthTraversal("generated test bodies; the self-calls are `new(` helpers"),
    ),
    (
        "term_wrapper.rs",
        "semantic_hash",
        Coverage::NotADepthTraversal(
            "a DISPATCHER: forwards `clone`/`semantic_hash`/`substitute_env` to the per-category \
             drivers, which are measured on their own. Its own recursion depth is 1",
        ),
    ),
    (
        "language_trait_impl.rs",
        "infer_var_type",
        Coverage::NotADepthTraversal(
            "a DISPATCHER onto `var_inference.rs`'s walk, which carries the row above",
        ),
    ),
    (
        "env_types.rs",
        "new",
        Coverage::NotADepthTraversal("an environment container; the self-calls are `new(`"),
    ),
    (
        "metadata.rs",
        "nth_index",
        Coverage::NotADepthTraversal("static grammar metadata tables; `nth_index` is a helper"),
    ),
    (
        "rho_fold_dataflow.rs",
        "__mettail_rho_dataflow_collect_int",
        Coverage::NotADepthTraversal("fixed-arity dataflow shim, no term-depth recursion"),
    ),
    (
        "rho_scalar_invocation.rs",
        "__mettail_rho_try_scalar_inner",
        Coverage::NotADepthTraversal("fixed-arity scalar shim, no term-depth recursion"),
    ),
    // ── files with no self-recursive call at all ────────────────────────────────────
    ("ast_enums.rs", "", Coverage::Inert),
    ("ast.rs", "", Coverage::Inert),
    ("binder_congruence.rs", "", Coverage::Inert),
    ("flatten.rs", "", Coverage::Inert),
    ("freshness.rs", "", Coverage::Inert),
    ("guard_codegen.rs", "", Coverage::Inert),
    ("language.rs", "", Coverage::Inert),
    ("numeric_cast_adapter.rs", "", Coverage::Inert),
    ("rust_ctor.rs", "", Coverage::Inert),
    ("simulate.rs", "", Coverage::Inert),
    ("tests_analytical.rs", "", Coverage::Inert),
    ("tests_rewrite.rs", "", Coverage::Inert),
    ("tests_unit.rs", "", Coverage::Inert),
];

/// ⚠ The non-vacuity floor on the DERIVED file universe. If the scan ever returned
/// nothing — a relocated `target`, a rename, a build that did not run the macro — every
/// assertion below would iterate an empty set and PASS. It may only grow.
const MIN_GENERATED_FILES: usize = 40;

/// Historical closure ledger for the generated-traversal exception set.
///
/// ⚠ **This doc used to say "alongside the seven already on file" while the constant read
/// 6.** The sentence was written when the value was 7 and was not moved when the #189
/// residual took `eval.rs` out. ⇒ The membership is spelled ONCE, immediately below, and
/// nowhere else in this file; every other site refers to this constant by name.
///
/// ★ 7 → 6 (#189 residual, 2026-07-30). The new value is **DERIVED, not decremented**: the
/// census was run with the old value still in place and its own failure reported the count
/// and the membership —
///
/// ```text
/// the count of UNMEASURED host-recursive traversals is 6 and the ratchet says 7:
/// ["env_subst.rs", "parse_alt_filter.rs", "var_inference.rs", "language_struct.rs",
///  "flt_reflect.rs", "dovetail_report.rs"]
/// ```
///
/// — and 6 is what was then written here. Subtracting one from seven would have produced the
/// same number and proved nothing; letting the instrument answer is what makes the figure a
/// measurement.
///
/// ★ 6 → 5 (2026-07-31): `env_subst.rs` was not converted in this change; inspection of the
/// emitted artifact established that it had already been generated as
/// `SUBST_TASK_POOL` → `subst_iterative`. The old detector counted the fixed-point wrapper's
/// repeated method calls as recursive descent. `ast_env_subst` independently exercises the
/// environment-only `SubstOp::EnvProc` arm on a deep leaf substitution, so the row moves to
/// `Subject` only together with a non-vacuous main-thread depth probe.
///
/// ★ 5 → 4 (2026-07-31): `parse_alt_filter.rs` now folds its two disjunctive flags with
/// `UNIFORM_TASK_POOL` → `uniform_flags_iterative`. The conversion has no result stack:
/// both joins are associative/commutative/idempotent, and a native literal is an absorbing
/// negative verdict for the public predicate. `ast_parse_alt_filter` supplies the independently
/// captured red/green depth witness through a same-category `Add` spine whose deepest node is the
/// auto-injection-equivalent `POutputEmpty` wrapper the filter must reach.
///
/// ★ 4 → 3 (2026-07-31): both ordered variable-inference visitors now share
/// `INFERENCE_TASK_POOL`. Fields and collection positions are pushed in reverse so LIFO pop order
/// exactly preserves the former recursive first-match order; HOL application frames retain their
/// immediate function-position type rule before queuing lambda then domain-typed arguments.
/// `ast_var_inference` records the red overflow and the flat green traversal to a deepest free var.
///
/// ★ 3 → 2 (2026-07-31): every `collect_all_*_vars` function now drives a pooled local task
/// PDA. Visit/Binder/MultiBinder phases preserve first-seen order without cloning/unbinding
/// scopes, and the shared collection boundary visits both map positions plus only Set PathMap
/// values. `ast_language_var_collect` has an independent pre-conversion overflow artifact and a
/// deepest-free-variable anti-vacuity assertion.
///
/// ★ 2 → 1 (2026-07-31): all mutually recursive `__mettail_rho_net_reflect_*` functions now
/// seed one pooled heterogeneous task PDA. Assemble frames preserve positional child order;
/// HashBag/HashSet task ranges are reversed in place so prior iterator order is retained;
/// fail-closed errors are reached in the same depth-first order. `ast_flt_reflect` bypasses the
/// parser through `FltReflect::reflect_flt_term`, records the recursive RED overflow, and measures
/// the generated PDA flat on the main-thread stack. `GroundTerm` Clone/Eq/Debug/Drop and FLT hole
/// normalization are independently iterative so result lifecycle cannot reintroduce recursion.
///
/// ★ 1 → 0 (2026-07-31): typed Dovetail lowering and reconstruction now use one shared,
/// pooled heterogeneous PDA per language. The exact derivation key is a persistent prefix-coded
/// tree with iterative lifecycle; it replaces the recursively re-escaped byte representation
/// whose time and space doubled at each depth. `ast_dovetail_report` reaches depth 16,384 on a
/// 1 MiB main-thread stack with `RUST_MIN_STACK` unset. The zero state is represented by the
/// absence of an exception variant, so a future traversal cannot be "temporarily" classified
/// as unmeasured.

/// `target/generated/rholang`, derived from the probe binary's own path so it survives a
/// relocated `CARGO_TARGET_DIR` and `cargo nextest`'s archive layout.
fn generated_dir() -> std::path::PathBuf {
    let probe = std::path::Path::new(PROBE);
    let target = probe
        .parent()
        .and_then(|debug| debug.parent())
        .expect("stack_depth_gate: the probe path has no <target>/<profile>/ prefix");
    target.join("generated").join("rholang")
}

/// Whether `source` contains a call to a function it also DEFINES — the cheap, single-pass
/// marker for "this file recurses". One pass over the text, so it is affordable on the
/// 239k-line `wpda.rs`.
///
/// ⚠ Deliberately LOOSE in the safe direction: it counts helper reuse (`new(`) as
/// recursion, which is why the table classifies rather than merely counts. A loose
/// detector over-reports and forces a row; a tight one would under-report and let a
/// traversal through, which is the failure that produced #189.
fn defines_a_function_it_also_calls(source: &str) -> bool {
    let mut defined: std::collections::HashSet<&str> = std::collections::HashSet::new();
    let mut called: std::collections::HashSet<&str> = std::collections::HashSet::new();
    let bytes = source.as_bytes();
    let is_word = |b: u8| b.is_ascii_alphanumeric() || b == b'_';
    let mut i = 0usize;
    while i < bytes.len() {
        if !is_word(bytes[i]) || (i > 0 && is_word(bytes[i - 1])) {
            i += 1;
            continue;
        }
        let start = i;
        while i < bytes.len() && is_word(bytes[i]) {
            i += 1;
        }
        let word = &source[start..i];
        // Is it followed by `(` or `<`, i.e. is this a definition or a call site?
        let mut j = i;
        while j < bytes.len() && (bytes[j] == b' ' || bytes[j] == b'\n' || bytes[j] == b'\t') {
            j += 1;
        }
        if j >= bytes.len() || (bytes[j] != b'(' && bytes[j] != b'<') {
            continue;
        }
        // Preceded by `fn `?
        let preceded_by_fn = start >= 3 && &source[start - 3..start] == "fn ";
        if preceded_by_fn {
            defined.insert(word);
        } else {
            called.insert(word);
        }
    }
    defined.intersection(&called).next().is_some()
}

/// ★★ **THE #189 GATE — every generated file is classified, and every depth traversal has a
/// probe subject.**
///
/// Four assertions, and each catches a distinct way the census can go stale:
///
/// 1. **A new generated file appears** and is not classified. This is the direction that
///    would have caught `is_ground` — a new emitter writes a new file, and the file set is
///    derivable while the subject table is not.
/// 2. **A declared file disappears**, so the row describes nothing.
/// 3. **A row claiming `Inert` describes a file that recurses** — a traversal smuggled
///    into a file that was previously inert.
/// 4. **A row claiming a subject names one the probe does not dispatch** — the link
///    between this table and `EXPECTED_DRIVER_SHAPE` is checked rather than assumed.
///
#[test]
fn every_generated_traversal_has_a_probe_subject() {
    let dir = generated_dir();
    let mut present: Vec<String> = std::fs::read_dir(&dir)
        .unwrap_or_else(|e| {
            panic!(
                "stack_depth_gate: could not read the generated tree at {}: {e}. The census \
                 derives its universe from this directory; without it every assertion below \
                 would be vacuous.",
                dir.display()
            )
        })
        .filter_map(|entry| entry.ok())
        .map(|entry| entry.file_name().to_string_lossy().into_owned())
        .filter(|name| name.ends_with(".rs"))
        .collect();
    present.sort();

    assert!(
        present.len() >= MIN_GENERATED_FILES,
        "stack_depth_gate: only {} generated `.rs` files found in {}, below the floor of {}. \
         Either the macro did not run or the layout moved — and an under-populated scan makes \
         every assertion below pass vacuously.",
        present.len(),
        dir.display(),
        MIN_GENERATED_FILES
    );

    // (1) TOTALITY, derived direction: every generated file is classified.
    for name in &present {
        assert!(
            GENERATED_FILE_CENSUS
                .iter()
                .any(|(declared, _, _)| declared == name),
            "UNCLASSIFIED GENERATED FILE `{name}`: the macro writes it and \
             `GENERATED_FILE_CENSUS` does not say what it is.\n\
             ★ This is the assertion that exists because of #189. A new generated traversal \
             arrives as a new FILE, and the file set is derivable while \
             `stack_depth_probe`'s `SUBJECTS` table is not — so a driver with no subject was \
             invisible to `the_sloped_driver_set_is_exactly_the_declared_one`, which totals \
             over the subject table. Classify it as `Subject(..)` with a non-vacuous probe, \
             `NotADepthTraversal(..)` only when recursion is provably not bounded by host-term \
             depth, or `Inert` when it does not recurse at all."
        );
    }

    // (2) TOTALITY, declared direction: no rows for files that no longer exist.
    for (declared, _, _) in GENERATED_FILE_CENSUS {
        assert!(
            present.iter().any(|name| name == declared),
            "STALE CENSUS ROW `{declared}`: it is classified here but the macro no longer \
             writes it. A removed file must lose its row, or the table stops being a \
             description of anything."
        );
    }

    // (3) An `Inert` row must describe a file that really does not recurse, and a
    //     traversal row must name an entry point that is really still there.
    let mut lies: Vec<String> = Vec::new();
    for (file, entry, coverage) in GENERATED_FILE_CENSUS {
        let source = std::fs::read_to_string(dir.join(file))
            .unwrap_or_else(|e| panic!("stack_depth_gate: could not read {file}: {e}"));
        match coverage {
            Coverage::Inert => {
                if defines_a_function_it_also_calls(&source) {
                    lies.push(format!(
                        "  {file} is declared INERT but now defines a function it also calls. \
                         A traversal has been added to a file that was not one. Reclassify it \
                         — with a subject if it descends a host term."
                    ));
                }
            },
            _ => {
                if !entry.is_empty() && !source.contains(entry) {
                    lies.push(format!(
                        "  {file} is declared to contain the entry point `{entry}`, and it does \
                         not. Either it was renamed (update the row) or the traversal was \
                         removed (remove the row) — a row that describes nothing is worse than \
                         no row, because it reads as coverage."
                    ));
                }
            },
        }
    }
    assert!(lies.is_empty(), "GENERATED-FILE CENSUS IS WRONG:\n{}", lies.join("\n"));

    // (4) Every declared subject is one the probe actually dispatches.
    let enumerated = probe_subjects();
    for (file, _, coverage) in GENERATED_FILE_CENSUS {
        if let Coverage::Subject(subject) = coverage {
            assert!(
                enumerated.iter().any(|name| name == subject),
                "`{file}` claims coverage by the probe subject `{subject}`, and the probe does \
                 not dispatch it. The claim of coverage is the thing under test here, so an \
                 unresolvable subject name is a silent hole of exactly #189's kind."
            );
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
/// *lowering* subject in this binary, `lower_width`, bisects to 73,728 B — the figure here
/// read 98,304 B when it was written and is corrected rather than deleted, because a 25 %
/// drift in an intercept is the kind of number that is worth knowing has moved. The
/// cheapest subject overall is `ast_is_ground` / `ast_clone` at 28,672 B, which is where
/// #187's instrument-floor question lands: 2.3× the floor, so still a measurement.) Below
/// depth
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
/// This historical build's asymptote was **1,408 B/level**, stable to the byte across the last
/// three intervals. The parse path in that build was therefore Θ(depth), although it was never
/// the binding constraint: 10.7× cheaper than the M-1 lowering (15,132) and 34× cheaper than
/// the original (48,392).
///
/// ★ **The methodological lesson, which generalises past this subject.** The module
/// header warns that a large intercept with a small slope passes a FIXED-STACK
/// ladder while still being Θ(depth). This is that hazard's dual: a large intercept
/// with a small slope also reads as *zero slope* on a ladder that never leaves the
/// intercept-dominated regime. Both probe points of a slope measurement must sit
/// clear of the subject's own floor, or the derived slope is understated — here, to
/// zero. That is why the permanent gate probes 4 and 4,096 rather than using only
/// the 16 and 128 that produced the retracted claim.
///
/// **Living disposition (2026-08-03).** Rebuilt against f1r3node `26876b65`, the current
/// production path requires the same minimum native stack at depths 512 and 4,096:
/// **0 B/step**. The later generated semantic-hash and collection-element driver conversions
/// removed the native-stack growth exercised while parsing and tearing down this fixture; the
/// parser algorithm itself was not rewritten as part of this closure. The historical knee is
/// retained above because it explains why a narrow ladder is not acceptable evidence.
#[test]
fn parsing_is_depth_independent() {
    assert_depth_independent("parse_depth", 1024 * 1024);
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
    // The parser and lowering are now independently flat. Depth 4,096 remains a useful
    // end-to-end witness because it is far beyond the original failure and exercises both
    // machines without turning this smoke assertion into an unbounded resource test.
    assert!(
        runs_within(DEFAULT_MAIN_THREAD_STACK, 4096, "reproducer"),
        "REGRESSION: `@\"OUT\"!([[…[1]…]])` at depth 4,096 no longer survives parse+lower on \
         an {} MiB stack — the reported SIGSEGV is back or worse.",
        DEFAULT_MAIN_THREAD_STACK / (1024 * 1024)
    );
}

/// ★★ **#187 — THE INSTRUMENT'S OWN FLOOR, ASSERTED RATHER THAN ASSUMED.**
///
/// Three claims, and each is a thing a reader would otherwise have to take on trust:
///
/// 1. **The floor is REAL.** One rung below [`SMALLEST_POSEABLE_STACK`] the instrument
///    genuinely cannot pose the question: `execve` fails with `E2BIG` because Linux
///    requires the child's `argv` + `envp` block to fit inside the new `RLIMIT_STACK`. If
///    this ever starts *succeeding*, the floor has moved and the constant is stale — which
///    matters, because the constant is what separates "unresolved" from "12,288 B".
/// 2. **The floor is REPORTED, not disguised.** A reading below it must render as
///    `<12 KiB (BELOW THE INSTRUMENT FLOOR)`. [`MinStack`] makes that structural — there is
///    no `usize` for the caller to mistake for a measurement — and this row pins the
///    rendering, because the whole defect was a value that *looked* like a measurement.
/// 3. **No subject currently sits on the floor**, so every absolute figure this gate prints
///    today is a measurement. That is a MEASURED claim about this build, not a property of
///    the design: the cheapest subject in the binary bisects to 28,672 B, 2.3× the floor. If a
///    leaner build ever puts a subject under it, the instrument now says so instead of
///    quoting 12,288.
///
/// ⚠★★ **A SECOND TRAP IN THE SAME FAMILY, and it belongs where the instrument is
/// documented: a slope measured from a SINGLE derived function does not transfer to a FAMILY
/// of free functions that reproduces it.**
///
/// The worked case is `f1r3node-rust-mettail`'s `clone_oracle` — a hand-written family of
/// free functions proved *semantically* identical to the pre-conversion
/// `<Par as Clone>::clone` (byte-identical on eight axes over 67 enumerated shapes,
/// `models/tests/clone_equivalence_corpus.rs`). Semantic identity is not frame-layout
/// identity, and the divergence is PROFILE-DEPENDENT:
///
/// ```text
///                    oracle (family of free fns)      derive (one function)
///   debug                    16,128 B/level               16,493 B/level    − 2.2 %
///   release                   7,021 B/level                3,254 B/level    + 116 %
/// ```
///
/// Under `-O` a family of free functions inlines differently from one
/// `<Par as Clone>::clone`, and the family costs **2.16×** more per level. Both numbers are
/// correct about what they measured; only 3,254 answers "what does the derive cost".
///
/// ⇒ **The rule.** A per-level cost is a property of the *call chain that actually exists*,
/// not of the semantics it implements. Re-measure after any change that splits or merges the
/// functions in a chain, and never carry a slope across such a change — in debug you may get
/// away with it (2.2 % here), in release you will not (116 %).
///
/// ★ Two qualifications that make the rule usable rather than merely alarming. First, the
/// divergence there is CONSERVATIVE for every leg that uses the oracle as a *control*: those
/// legs want the control to be expensive, so an over-costly control cannot manufacture a
/// false green. Second, it is the RELEASE profile that diverges, so a debug-only
/// cross-validation between a proxy and the real thing is weak evidence that they agree.
#[test]
fn the_instrument_floor_is_reported_and_no_subject_sits_on_it() {
    // (1) One rung below the floor, the question cannot be posed at all.
    let below = SMALLEST_POSEABLE_STACK - RESOLUTION;
    assert!(
        !runs_within(below, 4, "ast_clone"),
        "#187: `ast_clone` now SURVIVES an `RLIMIT_STACK` of {below} B, one {RESOLUTION}-byte \
         rung below `SMALLEST_POSEABLE_STACK`. Measured 2026-07-30 that bound made `execve` \
         itself fail with `E2BIG` (Linux requires the child's argv+envp block to fit inside \
         the new stack), so the floor constant was derived from where the instrument stops \
         being able to ASK. If a child now runs there, the floor has moved and \
         `SMALLEST_POSEABLE_STACK` is stale — which makes the difference between `unresolved` \
         and a {SMALLEST_POSEABLE_STACK} B reading wrong in the direction that hides a \
         subject."
    );

    // (2) The unresolved case NEVER renders as a number.
    let rendered = MinStack::BelowResolution.to_string();
    assert!(
        !rendered.contains(&SMALLEST_POSEABLE_STACK.to_string())
            && rendered.contains("BELOW THE INSTRUMENT FLOOR"),
        "#187: `MinStack::BelowResolution` renders as {rendered:?}. It must not be mistakable \
         for a measurement — the entire defect was that a floored bisection returned the \
         floor VALUE, so twelve unresolved subjects read as twelve agreeing measurements of \
         12 KiB. It has to say it is a bound."
    );

    // (3) No subject sits on the floor on this build. Scoped to the three cheapest subjects
    //     in the binary — a full sweep would be ~45 bisections and these are the only
    //     candidates, since every other subject's floor is strictly above theirs.
    for name in ["ast_clone", "ast_is_ground", "lower_width"] {
        let measured = measure_min_stack(name, 4);
        assert!(
            matches!(measured, MinStack::Bytes(bytes) if bytes > SMALLEST_POSEABLE_STACK),
            "#187: `{name}` measured {measured} at parameter 4. It is at or below the \
             instrument floor, so its absolute reading is a BOUND and not a value.\n\
             This is not automatically a defect — a cheaper build is good news — but every \
             absolute figure derived from it (the audit's §9 tables, the stack-safety report) \
             must be restated as `<= {} B` rather than as a number, and \
             `assert_no_slope_over_baseline` will now refuse to derive \
             from it. ★ The SLOPE conclusions are unaffected: flat between two floored points \
             still establishes flatness (see `assert_no_slope`).",
            SMALLEST_POSEABLE_STACK
        );
    }
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
        ("parse_depth", &[4, 512, 4096]),
        ("parse_width", &[4, 16, 64, 128]),
        ("reproducer", &[4, 16, 64, 128]),
        // ★ Former residues, retained in the reporter as zero-slope regression evidence.
        ("par_drop", &[4, 512, 4096]),
        ("par_hash", &[4, 512, 4096]),
        ("par_hashmap", &[4, 512, 4096]),
        ("ast_drop", &[512, 4096]),
        ("render", &[512, 4096]),
    ];
    // ★★ #187 — THESE FIFTEEN ROWS ARE THE INSTRUMENT-FLOOR EXHIBIT, and the reason this
    // reporter changed shape.
    //
    // It printed one absolute byte count per rung and then divided the endpoints, so a
    // subject sitting on the bisection floor produced the line `name,4,12288` — a number
    // indistinguishable from a genuine 12,288 B measurement — and a derived slope of
    // `(12288 - 12288)/span = 0.0` that looked like a result. Twelve such rows read as
    // twelve agreeing measurements and are ONE floor showing through. See
    // `SMALLEST_POSEABLE_STACK`.
    //
    // Now: a floored rung prints `BELOW-FLOOR` rather than a number, and the derived slope
    // is printed only when BOTH endpoints resolved. When either is floored the slope line
    // says which end could not be resolved, because a bound is a different claim from a
    // value and a reader must not have to infer which one is on the page.
    println!("subject,param,min_stack_bytes");
    for (name, ladder) in subjects {
        let mut points: Vec<(usize, MinStack)> = Vec::with_capacity(ladder.len());
        for &p in *ladder {
            let s = measure_min_stack(name, p);
            match s {
                MinStack::Bytes(bytes) => println!("{name},{p},{bytes}"),
                MinStack::BelowResolution => println!(
                    "{name},{p},BELOW-FLOOR (<={}) # unresolved; the instrument cannot pose a \
                     smaller bound",
                    SMALLEST_POSEABLE_STACK
                ),
            }
            points.push((p, s));
        }
        let (p0, s0) = points[0];
        let (p1, s1) = points[points.len() - 1];
        match (s0, s1) {
            (MinStack::Bytes(b0), MinStack::Bytes(b1)) => {
                let slope = (b1 as f64 - b0 as f64) / (p1 as f64 - p0 as f64);
                println!("# {name}: {slope:.1} B/step over {p0}..{p1}");
            },
            _ => println!(
                "# {name}: SLOPE NOT DERIVED over {p0}..{p1} — {p0} read {s0} and {p1} read \
                 {s1}. Dividing a difference of floored readings yields the FLOOR's slope, \
                 not the subject's. Raise the ladder until both ends clear {} B, or state \
                 the result as the bound `<= {} B at both ends`, which is still enough to \
                 establish FLATNESS (see `assert_no_slope`).",
                SMALLEST_POSEABLE_STACK, SMALLEST_POSEABLE_STACK
            ),
        }
    }
}
