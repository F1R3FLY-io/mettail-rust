//! CI gate for the **Computed Desk** demo (`demos/flt-lookahead/`).
//!
//! The demo's vehicle is the `rhocalc` interpreter binary run on a committed `.rho` file, so
//! this file drives that binary with the run sheet's own command line and asserts what the
//! audience sees. Without it the run sheet is a hand-run narrative that rots silently — the
//! same reasoning `church_desk_demo.rs` is built on.
//!
//! ## ★ What this gate is FOR, beyond "the transcript still matches"
//!
//! The demo's whole claim is that the numerals on `@"results"` are values the machine
//! **computed**. A demo whose inputs are transcribed constants would produce the identical
//! transcript, so the transcript alone proves nothing. Two cells therefore assert the claim
//! rather than the output:
//!
//! * [`the_demo_source_contains_no_transcribed_answer`] — the `.rho` file's *program* (its
//!   comments stripped) does not contain either Church numeral. It cannot be sending an
//!   answer it was given.
//! * [`the_demo_reports_that_the_lookahead_ran`] — the run reports two **served** requests.
//!   A run in which the engine was missing would report unserved requests and exit non-zero.

#![cfg(all(
    feature = "rhocalc-runtime",
    feature = "lambda-runtime",
    feature = "calculator-runtime"
))]

use std::path::PathBuf;
use std::process::{Command, Output};

/// The demo directory, relative to the workspace root.
const DEMO_DIR: &str = "demos/flt-lookahead";
/// The committed program the run sheet runs.
const PROGRAM: &str = "demos/flt-lookahead/01-computed-desk.rho";

/// The workspace root — `rholang-runtime/..`.
fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("the runtime crate has a parent workspace directory")
        .to_path_buf()
}

/// Run the built `rhocalc` binary on `path`, exactly as the run sheet does.
///
/// `RUST_MIN_STACK` is set for the same reason the run sheet sets it: the λ terms below drive
/// a deep recursive lowering, and the default 2 MiB test-thread stack is not enough.
fn rhocalc(path: &str) -> Output {
    Command::new(env!("CARGO_BIN_EXE_rhocalc"))
        .current_dir(workspace_root())
        .env("RUST_MIN_STACK", "8388608")
        .arg(path)
        .output()
        .expect("the rhocalc binary must run")
}

fn transcript(output: &Output) -> String {
    format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    )
}

/// The demo's PROGRAM — the source with every `//` comment line removed.
///
/// The comment header explains what the answers are, so a naive grep over the whole file would
/// find "5" and "6" in prose. The claim is about the program.
fn program_without_comments() -> String {
    let source = std::fs::read_to_string(workspace_root().join(PROGRAM))
        .expect("the committed demo program must be readable");
    source
        .lines()
        .filter(|line| !line.trim_start().starts_with("//"))
        .collect::<Vec<_>>()
        .join("\n")
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// The transcript
// ════════════════════════════════════════════════════════════════════════════════════════════

/// ★ The demo runs, exits clean, and publishes the BODY of a computed Church numeral.
///
/// The republished value is `lam f. lam x. ${body}`'s `body`, so the numeral is read as the
/// nesting depth of the de-Bruijn application — five applications of `1` to `0` is the numeral
/// 5, which is `plus 2 3`.
#[test]
fn the_demo_publishes_a_computed_church_numeral() {
    let output = rhocalc(PROGRAM);
    let rendered = transcript(&output);
    eprintln!("{rendered}");
    assert!(output.status.success(), "the demo must exit clean:\n{rendered}");
    assert!(
        rendered.contains(r#"[0] ⟦(1 (1 (1 (1 (1 0)))))⟧"#),
        "★ the demo must publish the BODY of the Church numeral 5 — `plus 2 3`, β-reduced by \
         the machine inside a speculative tuplespace:\n{rendered}"
    );
}

/// The run reports that the lookahead actually ran: two requests SERVED, no branch failure,
/// no truncation.
#[test]
fn the_demo_reports_that_the_lookahead_ran() {
    let rendered = transcript(&rhocalc(PROGRAM));
    assert!(
        rendered.contains("lookahead: 2 request(s) served"),
        "both `[*]` sends must be served — an unserved one would be reported and would fail \
         the run:\n{rendered}"
    );
    assert!(
        rendered.contains("^spec-success: 2"),
        "one provenance datum per computed branch:\n{rendered}"
    );
    assert!(
        rendered.contains("^spec-failure: 0 · ^spec-truncated: 0"),
        "`[*]` over a terminating λ term runs to quiescence with nothing dead and nothing \
         cut short:\n{rendered}"
    );
}

/// The transcript is reproducible rather than a lucky schedule: three consecutive runs of the
/// same binary produce byte-identical output.
///
/// This is not decoration. The exploration is a breadth-first search over a tuplespace whose
/// enumeration order f1r3node derives from content, and the whole reason a trace is a content
/// digest is that two validators must agree on it. A schedule-dependent transcript would mean
/// the enumeration was not content-derived after all.
#[test]
fn the_demo_transcript_is_reproducible() {
    let first = transcript(&rhocalc(PROGRAM));
    for run in 2..=3 {
        assert_eq!(
            transcript(&rhocalc(PROGRAM)),
            first,
            "run {run} differed from run 1 — the exploration must not depend on the scheduler"
        );
    }
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// ★ The claim, not the output
// ════════════════════════════════════════════════════════════════════════════════════════════

/// ★★ **The demo's inputs are not its answers.** The program contains neither Church numeral.
///
/// This is the cell that separates this demo from `demos/flt-lambda-lab/04-desk.rho`, whose
/// three numerals are transcribed. If someone ever "simplifies" this file by pasting an answer
/// into it, the demo stops demonstrating anything and this test says so.
#[test]
fn the_demo_source_contains_no_transcribed_answer() {
    let program = program_without_comments();
    // The Church numerals 5 and 6, as this grammar spells them.
    for (numeral, spelling) in [
        (5, "(f, (f, (f, (f, (f, x)))))"),
        (6, "(f, (f, (f, (f, (f, (f, x))))))"),
    ] {
        assert!(
            !program.contains(spelling),
            "★ the demo program must not contain the Church numeral {numeral} — the whole \
             point is that the machine COMPUTES it. Found {spelling:?} in:\n{program}"
        );
    }
    // …and it does contain the two SUBJECTS, so the test cannot pass by the file being empty.
    assert!(
        program.contains("lam m. lam n. lam f. lam x."),
        "the program must still contain `plus`:\n{program}"
    );
    assert!(
        program.contains("lam m. lam n. lam f. (m, (n, f))"),
        "the program must still contain `mult`:\n{program}"
    );
    // Both sends carry the lookahead suffix; without it they are ordinary sends of inert terms.
    assert_eq!(
        program.matches(")[*]").count(),
        2,
        "both sends must carry the `[*]` suffix:\n{program}"
    );
}

/// Every command line the run sheet prints for the demo is driven by this file, so the
/// presenter's page cannot name a command nobody runs.
#[test]
fn every_run_sheet_command_line_is_driven_by_this_test() {
    let sheet = std::fs::read_to_string(workspace_root().join(DEMO_DIR).join("RUN-SHEET.md"))
        .expect("the run sheet must be readable");
    let invocations: Vec<&str> = sheet
        .lines()
        .map(str::trim)
        .filter(|line| line.contains("target/debug/rhocalc"))
        .collect();
    assert!(!invocations.is_empty(), "the run sheet must show how to run the demo");
    for invocation in invocations {
        assert!(
            invocation.contains(PROGRAM),
            "the run sheet invokes {invocation:?}, which this gate does not drive"
        );
    }
}

/// The transcript printed in the run sheet is the one the binary produces. A sheet that drifts
/// from the binary is worse than no sheet: it is a rehearsed claim nobody re-checked.
#[test]
fn the_run_sheet_transcript_is_the_observed_output() {
    let sheet = std::fs::read_to_string(workspace_root().join(DEMO_DIR).join("RUN-SHEET.md"))
        .expect("the run sheet must be readable");
    let observed = transcript(&rhocalc(PROGRAM));
    for line in [
        r#"    [0] ⟦(1 (1 (1 (1 (1 0)))))⟧"#,
        "  lookahead: 2 request(s) served · ^spec-success: 2 · ^spec-failure: 0 · ^spec-truncated: 0",
    ] {
        assert!(sheet.contains(line), "the run sheet must print {line:?}");
        assert!(
            observed.contains(line.trim_start()),
            "the run sheet prints {line:?}, which the binary did not produce:\n{observed}"
        );
    }
}
