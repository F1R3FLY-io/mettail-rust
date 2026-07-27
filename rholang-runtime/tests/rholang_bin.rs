//! CI gate for the `rholang` interpreter binary (`src/bin/rholang.rs`).
//!
//! Runs the built binary on the committed demo `.rho` files and asserts the RhoCalc programs —
//! which exercise the grammar's Foreign Language Term feature — actually evaluate on the f1r3node
//! reducer, so "the demos work" is CI-gated rather than a one-time manual check. The full path is
//! the rho-native one: the GENERATED RhoCalc parser → `PFlt` lowering (lam → LambdaLanguage) → the
//! real reducer (never a host/Dovetail simulation).
//!
//!  * `k-combinator.rho` — a bare λ-term `App(App(K, I), K)` EVALUATES TO ITS NORMAL FORM: it
//!    β-reduces in-Rho (`^fired` records the `Beta` firings) and `@"OUT"` rests at the identity
//!    `I = λ.0` (K kept its first argument, discarded the second).
//!  * `foreign-exchange.rho` — a PROCESS whose send/receive rendezvous fires as one COMM; the two
//!    typed `${x}` holes capture ⟦I⟧, ⟦K⟧ and the re-quote reconstructs App(I, K), resting on
//!    `@"OUT"` as `(λ.0 λ.λ.1)`.
#![cfg(all(feature = "rholang-runtime", feature = "lambda-runtime"))]

use std::path::PathBuf;
use std::process::{Command, Output};

/// Absolute path to a demo file under `<workspace>/demos/flt-foreign-exchange/`.
fn demo_path(file_name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../demos/flt-foreign-exchange")
        .join(file_name)
}

/// Run the built `rholang` binary on a demo file, capturing its output.
fn run_interpreter(demo_file: &str) -> Output {
    run_interpreter_with(demo_file, &[])
}

/// Run the built `rholang` binary on a demo file with extra flags.
fn run_interpreter_with(demo_file: &str, flags: &[&str]) -> Output {
    let mut command = Command::new(env!("CARGO_BIN_EXE_rholang"));
    command.args(flags).arg(demo_path(demo_file));
    command
        .env("RUST_MIN_STACK", "8388608")
        .output()
        .expect("the rholang binary must run")
}

#[test]
fn k_combinator_demo_beta_reduces_to_identity() {
    let output = run_interpreter("k-combinator.rho");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "rholang exited non-zero on k-combinator.rho\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    // (K I) K β-reduces on the reducer to the identity I = λ.0 (K discards its second argument).
    assert!(
        stdout.contains("⟦λ.0⟧"),
        "expected the β-normal form I = λ.0 on @\"OUT\"\nstdout:\n{stdout}"
    );
    // The reduction genuinely fired on the reducer — the ^fired ledger records the two Beta steps.
    assert!(
        stdout.contains("\"Beta\", \"Beta\""),
        "expected two Beta firings in the ^fired ledger\nstdout:\n{stdout}"
    );
    // And it did NOT merely echo the un-reduced input App(App(K, I), K).
    assert!(
        !stdout.contains("((λ.λ.1 λ.0) λ.λ.1)"),
        "the term must be reduced, not echoed un-reduced\nstdout:\n{stdout}"
    );
}

#[test]
fn foreign_exchange_demo_binds_typed_holes_and_reconstructs() {
    let output = run_interpreter("foreign-exchange.rho");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "rholang exited non-zero on foreign-exchange.rho\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    // The COMM fires; the two typed holes ${f}, ${k} capture ⟦I⟧, ⟦K⟧ and the re-quote
    // reconstructs App(I, K), which renders as (λ.0 λ.λ.1) on @"OUT".
    assert!(
        stdout.contains("(λ.0 λ.λ.1)"),
        "expected the reconstructed App(I, K) = (λ.0 λ.λ.1) on @\"OUT\"\nstdout:\n{stdout}"
    );
}

// ── Task #18 — comments are LEXED and RETAINED, not stripped ─────────────────────────────────────

/// Both demos carry large explanatory comment headers — including prose that MENTIONS FLT openers
/// with unbalanced back-ticks and `${…}` holes. Under the retired `strip_comments` preprocessor
/// those bytes were deleted before the parser ever ran; they are now lexed as tokens routed to the
/// `COMMENTS` channel, consumed as trivia by the parse, and retained with their source positions.
///
/// That the demos still evaluate (the two tests above) proves NON-PERTURBATION on real programs;
/// that the interpreter reports a non-zero retained count proves RETENTION is live end-to-end.
#[test]
fn demos_retain_their_comments_on_the_comments_channel() {
    for demo in ["k-combinator.rho", "foreign-exchange.rho"] {
        let output = run_interpreter(demo);
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert!(
            output.status.success(),
            "rholang exited non-zero on {demo}\nstdout:\n{stdout}\nstderr:\n{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(
            stdout.contains("retained on the COMMENTS channel"),
            "expected {demo}'s comment header to be RETAINED, not stripped\nstdout:\n{stdout}"
        );
    }
}

/// `--emit-comments` dumps the retained channel with source positions. This is an out-of-band
/// BACKEND diagnostic; it is never data on a program-observable channel (no `@"COMMENTS"`, no
/// injected send), which is why the comment TEXT is printed only under the explicit flag.
#[test]
fn emit_comments_dumps_the_retained_channel_with_positions() {
    let output = run_interpreter_with("k-combinator.rho", &["--emit-comments"]);
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        output.status.success(),
        "rholang --emit-comments exited non-zero\nstdout:\n{stdout}"
    );
    // The demo's header opens on line 1, column 1 with a box-drawing rule — proof that the
    // position is the TRUE source position and that non-ASCII comment text survives intact.
    assert!(
        stdout.contains("  1:1: // ═══"),
        "expected the line-1 header comment dumped at its true position\nstdout:\n{stdout}"
    );
}
