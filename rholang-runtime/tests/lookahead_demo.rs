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

/// Every committed program the run sheet runs, in beat order.
///
/// ★ This was a single `PROGRAM` constant naming only beat 1. Beats 2 and 3 were added to the
/// run sheet without extending it, so [`every_run_sheet_command_line_is_driven_by_this_test`]
/// — whose whole job is to fail when the sheet names a command nobody runs — was itself red,
/// and stayed red because nothing else pointed at it. A gate that names one member of a set it
/// claims to cover is worse than no gate: it reads as coverage.
const PROGRAMS: &[&str] = &[
    "demos/flt-lookahead/01-computed-desk.rho",
    "demos/flt-lookahead/02-the-desk.rho",
    "demos/flt-lookahead/03-predicate.rho",
    "demos/flt-lookahead/04-divergence.rho",
];

/// Beat 1 — the program the transcribed-answer cell interrogates.
const PROGRAM: &str = PROGRAMS[0];

/// The workspace root — `rholang-runtime/..`.
fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("the runtime crate has a parent workspace directory")
        .to_path_buf()
}

/// Run the built `rhocalc` binary on `path`, exactly as the run sheet does.
///
/// ★ `RUST_MIN_STACK` is deliberately **removed from the environment**, not merely left unset:
/// the harness must reproduce what a presenter at a terminal gets, and the cell
/// [`no_run_sheet_command_line_raises_the_stack`] asserts the sheet carries no prefix. A gate
/// that quietly ran the binary in a roomier environment than the documented one would let the
/// sheet drift from reality in exactly the direction nobody checks.
///
/// `env_remove` rather than nothing at all, because the ambient environment may carry the
/// variable from an outer `cargo` invocation.
fn rhocalc(path: &str) -> Output {
    Command::new(env!("CARGO_BIN_EXE_rhocalc"))
        .current_dir(workspace_root())
        .env_remove("RUST_MIN_STACK")
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
/// The run sheet's **shell lines** — every non-empty line inside a fenced code block, trimmed.
///
/// This is the single definition of *"a command the sheet tells a presenter to type"*, and both
/// run-sheet gates are built on it. They previously used two different notions — one matched any
/// line containing `target/debug/rhocalc`, the other matched three hardcoded environment-
/// assignment prefixes — so the sheet had two inconsistent ideas of what a command was, and the
/// prefix list would silently miss a fourth spelling.
///
/// Working from the fence rather than from patterns also makes the prose/command distinction
/// structural instead of heuristic: explaining a retired incantation in a paragraph is free,
/// while putting it in a block a presenter would copy is not.
///
/// Transcript blocks (the expected-output samples) are included, which is harmless for both
/// callers: they are asserted against observed output elsewhere, and an output line that
/// invoked the binary or set the variable would be a genuine defect in the sheet.
fn run_sheet_shell_lines() -> Vec<&'static str> {
    // Leaked so callers get `&'static str` and can hold borrowed slices without threading a
    // lifetime through every gate. The sheet is a few kilobytes read once per test process.
    let sheet: &'static str = Box::leak(
        std::fs::read_to_string(workspace_root().join(DEMO_DIR).join("RUN-SHEET.md"))
            .expect("the run sheet must be readable")
            .into_boxed_str(),
    );
    let mut inside = false;
    let mut lines = Vec::new();
    for line in sheet.lines() {
        let trimmed = line.trim();
        // A fence is ``` possibly followed by an info string; toggling on every fence handles
        // both the opening and closing marker without tracking which is which.
        if trimmed.starts_with("```") {
            inside = !inside;
            continue;
        }
        if inside && !trimmed.is_empty() {
            lines.push(trimmed);
        }
    }
    lines
}

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
/// ★ This cell iterates **`PROGRAMS`**, not `PROGRAM`. It used to check beat 1 alone, and beat 1
/// happens to be the one beat that publishes no trace digest — so the cell was green while the
/// interpreter's injection randomness was drawn from OS entropy on every run, making beat 4's
/// `^spec-failure` line different every time. Widening the loop is the entire fix to the gate;
/// the defect it then exposed is documented on `run::deploy_rand`.
///
/// The lesson generalises past this file: a reproducibility cell scoped to a subset of the
/// artifacts it claims to cover reads as coverage and is not.
/// Three consecutive runs of one beat produce byte-identical output.
///
/// ★ Split one-test-per-beat rather than looped inside a single test, and not to dodge a
/// timeout. Reproducibility of each committed demo is an **independent property**, and the test
/// is nextest's unit of both parallelism and timeout — so four tests is the honest modelling,
/// runs the four beats concurrently instead of serially, and names the failing beat in the test
/// name rather than only in an assertion message. Looped, this took 300 s and tripped the
/// slow-timeout; the fix is the modelling, not a larger budget.
fn assert_beat_is_reproducible(program: &str) {
    let first = transcript(&rhocalc(program));
    for run in 2..=3 {
        assert_eq!(
            transcript(&rhocalc(program)),
            first,
            "{program}: run {run} differed from run 1 — the exploration must not depend on the \
             scheduler, and the injection randomness must be derived from the program"
        );
    }
}

#[test]
fn beat_1_computed_desk_is_reproducible() {
    assert_beat_is_reproducible(PROGRAMS[0]);
}

#[test]
fn beat_2_the_desk_is_reproducible() {
    assert_beat_is_reproducible(PROGRAMS[1]);
}

#[test]
fn beat_3_predicate_is_reproducible() {
    assert_beat_is_reproducible(PROGRAMS[2]);
}

#[test]
fn beat_4_divergence_is_reproducible() {
    assert_beat_is_reproducible(PROGRAMS[3]);
}

/// This file's own source, for the two coverage cells that count call sites in it.
fn this_source() -> String {
    std::fs::read_to_string(
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/lookahead_demo.rs"),
    )
    .expect("this test file must be readable")
}

/// How many **call sites** of `helper(ARRAY[` this file contains.
///
/// ## ⚠ The trap this exists to avoid, which it fell into
///
/// [`every_beat_has_a_reproducibility_cell`] was written as
/// `source.matches("assert_beat_is_reproducible(PROGRAMS[").count()`. The search literal is
/// **itself** a occurrence of the substring it searches for, so the count was always one more
/// than the number of real call sites and the assertion `cells == PROGRAMS.len()` could never
/// hold. The cell was red from the commit that introduced it (`ba952d1a`), which is worse than
/// having no coverage cell: a permanently-red gate is indistinguishable from a flake and gets
/// ignored, and the thing it was guarding — a beat added without its own test — goes unguarded.
///
/// Two independent defences here, because one was evidently not enough:
///
/// 1. the needle is **assembled at run time**, so no line of this file contains it literally;
/// 2. only lines that **start with** the needle count, so a mention inside a comment or inside
///    a longer expression is not a call site.
fn call_sites(helper: &str, array: &str) -> usize {
    let needle = format!("{helper}({array}[");
    this_source()
        .lines()
        .filter(|line| line.trim_start().starts_with(&needle))
        .count()
}

/// ★ Every beat this gate knows about has a reproducibility cell — so adding a fifth beat to
/// [`PROGRAMS`] cannot silently go uncovered by the split above.
#[test]
fn every_beat_has_a_reproducibility_cell() {
    let cells = call_sites("assert_beat_is_reproducible", "PROGRAMS");
    assert_eq!(
        cells,
        PROGRAMS.len(),
        "PROGRAMS has {} beats but only {cells} call assert_beat_is_reproducible — a beat \
         added to the list without its own cell is uncovered",
        PROGRAMS.len()
    );
}

/// …and the counter itself is not vacuous: it finds the calls it is supposed to find, and it
/// does **not** count its own search literal.
///
/// ★ This is the cell that would have caught the defect above. A counting helper with no test
/// of its own is a measurement nobody measured.
#[test]
fn the_call_site_counter_counts_calls_and_not_itself() {
    assert!(
        call_sites("assert_beat_is_reproducible", "PROGRAMS") > 0,
        "the counter must find the real call sites"
    );
    assert_eq!(
        call_sites("a_helper_this_file_does_not_call", "PROGRAMS"),
        0,
        "…and must find nothing for a helper nobody calls — including this very line, which \
         mentions the name it is asking about"
    );
}

/// ★ The trace digest specifically, across processes — the diagnostic twin of the cell above.
///
/// [`the_demo_transcript_is_reproducible`] says *"some byte differs"*. This says *"the trace
/// digest differs"*, which is the difference between a bug report and a bisect. It exists
/// because the digest is the field that actually moved, and because it is the field a consumer
/// keys a branch by: `^spec-success`, `^spec-failure` and `^spec-truncated` all carry one, and
/// the truncated map's is the handle a program passes back to resume.
#[test]
fn the_trace_digest_is_the_same_in_two_processes() {
    let digest = |output: &Output| -> String {
        transcript(output)
            .lines()
            .find_map(|line| {
                line.split("trace 0x").nth(1).map(|rest| {
                    rest.split_whitespace()
                        .next()
                        .unwrap_or_default()
                        .to_string()
                })
            })
            .expect("the divergence beat must print a trace digest")
    };
    let program = "demos/flt-lookahead/04-divergence.rho";
    let first = digest(&rhocalc(program));
    let second = digest(&rhocalc(program));
    assert_eq!(
        first, second,
        "★ the trace digest must be a function of the program, not of the process. It folds the \
         `Produce`/`Consume` event hashes, which hash each datum's `random_state` — so an \
         entropy-seeded injection makes it fresh every run. See `run::deploy_rand`."
    );
}

/// ★★ THE CELL THAT PINS THE CAUSE, not the symptom — invariance under scheduler width.
///
/// The trace digest used to fold each selection's **store index**, which is not content: it is a
/// local address assigned by task-arrival order, because `HotStore` *prepends* and every branch
/// of a `|` is a detached `tokio::spawn`. That made the digest a function of how many worker
/// threads happened to race.
///
/// It is also the measurement that cracked the diagnosis, after a 20-runs-20-distinct-values
/// probe was read as proving entropy when it proved nothing — the trace is ~400 steps, so the
/// space of index labelings is astronomically large and all-distinct is equally what a scheduler
/// race predicts. The dose-response curve is what discriminated:
///
/// | `TOKIO_WORKER_THREADS` | runs | distinct digests |
/// |---|---|---|
/// | 1 | 5 | 1 |
/// | 2 | 12 | 2 (mode = the 1-thread value) |
/// | 32 | 20 | 20 |
///
/// A single-width run — which is all [`the_trace_digest_is_the_same_in_two_processes`] does —
/// cannot see an arrival-order dependence that both processes happen to share. This cell can.
///
/// ## ⚠ What this cell can and cannot see, and where the rest of the property lives
///
/// It compares a **transcript**: what the interpreter chose to print. The thing two validators
/// must agree on is what the deploy `produce`d into the tuplespace, and those are not the same
/// bytes. Two defects lived in the gap and neither reached a transcript — `reify` emitting a
/// channel's data in arrival order, and `resting_on` doing the same on the guest path — so this
/// cell was green throughout.
///
/// `tests/x8_publication_is_scheduler_invariant.rs` is the half that closes it: same idea, but
/// over the **published data** on all five report channels plus the reply channel, and over a
/// program whose leaf holds several data on **one** channel — a shape no committed demo
/// produces, which is precisely why the two defects were invisible.
///
/// **Two runs per width**, so a single differing run reads as a flake at that width rather than
/// as a width effect. That is the distinction the dose-response table above turned on: 2 threads
/// gave *two* distinct digests over twelve runs with the 1-thread value as the mode, which one
/// run per width would have reported as "2 threads is broken" or as "2 threads is fine"
/// depending on which sample it drew.
///
/// ★ **One test per width**, for the same three reasons the beats above are split: invariance at
/// each width is an independent property, the test is nextest's unit of both parallelism and
/// timeout, and the failing width should be in the test *name*. It is also a hard requirement
/// here — looped, one run of the divergence beat costs ≈ 28 s and 1 + 4×2 runs measured **288 s**
/// against the default profile's 300 s `terminate-after` (`.config/nextest.toml`). Split, each
/// cell is three runs and the four run concurrently.
const WIDTHS: &[&str] = &["1", "2", "8", "32"];

/// One run of the divergence beat at a given worker-thread count.
fn transcript_at_width(threads: &str) -> String {
    let output = Command::new(env!("CARGO_BIN_EXE_rhocalc"))
        .current_dir(workspace_root())
        .env_remove("RUST_MIN_STACK")
        .env("TOKIO_WORKER_THREADS", threads)
        .arg("demos/flt-lookahead/04-divergence.rho")
        .output()
        .expect("the rhocalc binary must run");
    transcript(&output)
}

fn assert_width_reproduces_the_single_threaded_transcript(threads: &str) {
    let baseline = transcript_at_width("1");
    assert!(
        baseline.contains("trace 0x"),
        "the baseline run must actually have produced a lookahead transcript, or every \
         comparison below holds for the wrong reason:\n{baseline}"
    );
    for run in 1..=2 {
        assert_eq!(
            transcript_at_width(threads),
            baseline,
            "★ TOKIO_WORKER_THREADS={threads}, run {run}: the transcript changed. Something \
             published is keyed by task-arrival order rather than by content — that is a value \
             two validators could disagree on without either being wrong. See \
             `speculation::delivery::step_digest`, and \
             `x8_publication_is_scheduler_invariant` for the same property over the published \
             DATA rather than over the printed transcript."
        );
    }
}

#[test]
fn the_transcript_does_not_depend_on_the_scheduler_width() {
    assert_width_reproduces_the_single_threaded_transcript(WIDTHS[0]);
}

#[test]
fn width_2_reproduces_the_single_threaded_transcript() {
    assert_width_reproduces_the_single_threaded_transcript(WIDTHS[1]);
}

#[test]
fn width_8_reproduces_the_single_threaded_transcript() {
    assert_width_reproduces_the_single_threaded_transcript(WIDTHS[2]);
}

#[test]
fn width_32_reproduces_the_single_threaded_transcript() {
    assert_width_reproduces_the_single_threaded_transcript(WIDTHS[3]);
}

/// ★ …and every width in [`WIDTHS`] has a cell, so adding a fifth width to the list cannot go
/// uncovered — the same guard [`every_beat_has_a_reproducibility_cell`] provides for the beats,
/// through the same counter, which is now tested.
#[test]
fn every_width_has_a_cell() {
    let cells = call_sites("assert_width_reproduces_the_single_threaded_transcript", "WIDTHS");
    assert_eq!(
        cells,
        WIDTHS.len(),
        "WIDTHS has {} entries but only {cells} cells drive one",
        WIDTHS.len()
    );
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
    for (numeral, spelling) in
        [(5, "(f, (f, (f, (f, (f, x)))))"), (6, "(f, (f, (f, (f, (f, (f, x))))))")]
    {
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
    let shell = run_sheet_shell_lines();
    let invocations: Vec<&str> = shell
        .iter()
        .copied()
        .filter(|line| line.contains("target/debug/rhocalc"))
        .collect();
    assert!(!invocations.is_empty(), "the run sheet must show how to run the demo");
    for invocation in invocations.iter() {
        assert!(
            PROGRAMS.iter().any(|program| invocation.contains(program)),
            "the run sheet invokes {invocation:?}, which this gate does not drive"
        );
    }
    // …and every program this gate knows about appears in the sheet, so the coverage holds in
    // both directions: the sheet cannot name an undriven command, and a driven beat cannot go
    // missing from the presenter's page.
    for program in PROGRAMS {
        assert!(
            invocations
                .iter()
                .any(|invocation| invocation.contains(program)),
            "{program} is driven by this gate but the run sheet never invokes it"
        );
    }
}

/// ★ The run sheet must NOT carry a `RUST_MIN_STACK` prefix.
///
/// It used to: `RUST_MIN_STACK=134217728`, attributed to "λ terms of this size exceed the
/// default thread stack". That attribution was wrong twice. The interpreter's parse and
/// lowering run in `#[tokio::main]`'s `block_on` body — i.e. on the **main** thread, whose size
/// that variable does not set (it is read only by `std::thread` spawn). And the demos do not
/// need it regardless: every committed `.rho` file in this directory was measured running green
/// with the variable unset entirely.
///
/// This cell asserts the absence so the incantation cannot creep back as folklore. If a demo
/// ever genuinely needs more stack, the fix is the traversal, not the environment — raising the
/// stack is explicitly not an accepted resolution in this tree.
#[test]
fn no_run_sheet_command_line_raises_the_stack() {
    // Prose ABOUT the retired incantation is wanted — it is why the incantation stays retired —
    // and it is admitted for free, because [`run_sheet_shell_lines`] yields only what is inside
    // a fenced block. Inside a fence, any mention of the variable IS a use of it, so this needs
    // no pattern for the spellings (`export X=`, `X= cmd`, `env X=`): the extraction already
    // decided what counts as a command.
    for line in run_sheet_shell_lines() {
        assert!(
            !line.contains("RUST_MIN_STACK"),
            "the run sheet must not raise the stack — the demos run at the default: {line:?}"
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
