//! CI gate for the **Guarded Settlement Desk** demo (`demos/rhocalc-settlement/`).
//!
//! The sibling FLT demo is gated by `rholang-runtime/tests/rhocalc_bin.rs`, which runs the
//! BUILT binary on the COMMITTED demo files and asserts the observables the run sheet claims.
//! This file is the same pattern for a demo whose vehicle is the REPL: it drives the built
//! `repl` binary with the run sheet's own command lines (piped on stdin, exactly as a
//! presenter types them) and asserts, per beat, what lands on which channel, what fires, and
//! what rests. Without it the run sheet is a hand-run narrative that rots silently.
//!
//! ## What is covered, and by which layer
//!
//! | layer | vehicle | answers |
//! |---|---|---|
//! | REPL transcript | `CARGO_BIN_EXE_repl` + the sheet's command lines | what the AUDIENCE sees: the `OUT:` line, the backend/artifact, the step trace, the typed refusal |
//! | runtime readback | `lower_rhocalc_proc` + multi-channel `get_data` | what RESTS — the vetoed datum still on `@"offer"`, which the REPL's single-channel `OUT` view cannot show |
//! | script integrity | `RUN-SHEET.md` / `settlement.env` parsing | every command line in the sheet is driven here; every name the env file binds is used by the sheet |
//!
//! The two layers are complementary, not redundant: "the guard vetoed" is `OUT: []` on the
//! REPL, but "and the rejected offer is still on the book" is only observable by reading a
//! SECOND channel of the SAME quiescent store (the `rho_implies_guard.rs` /
//! `guard_discharge_corpus.rs` discipline).
//!
//! ## ★ Pending rename (NOT performed here)
//!
//! `RhoCalc` becomes `Rholang`, `demos/rhocalc-settlement/` becomes `demos/rholang-settlement/`,
//! and `repl rhocalc` becomes `repl rholang`. Every occurrence of the CURRENT names in this file
//! is confined to the two constants below, [`DEMO_DIR`] and [`STARTUP_LANGUAGE`] — so the rename
//! is a two-line edit here. Nothing else names the language: the Beat-7 refusal is matched on
//! the rename-free part of the message (the message itself opens `RhoMachine backend for
//! language RhoCalc …`, which will move with the production code that emits it), and every
//! other needle names a BACKEND (`RhoMachine`, `Dovetail`) or another language (`Calculator`).
//!
//! ## ★ Defect D1 — a guard rejection does not backtrack to the next resting datum
//!
//! Beat 3's third command (`{ desk | offer!(55u32) | offer!(42u32) }`) is claimed by the run
//! sheet to settle the 42 deterministically. It does not: over 20 hand runs (2026-07-25) it
//! produced `OUT: [42]` 12 times and `OUT: []` 8 times. The run sheet states the CORRECT
//! semantics — a guarded receive with a satisfying datum available is an enabled COMM, and
//! resting instead is a stuck state the rho calculus does not permit — and the matcher is
//! incomplete:
//!
//! * `rspace++/src/rspace/space_matcher.rs::find_matching_data_candidate` returns the FIRST
//!   datum that matches SPATIALLY; the `where` guard is not consulted at that point.
//! * `…::extract_first_match` then evaluates the guard through `Match::check_commit`, and on
//!   rejection `continue`s to the next waiting CONTINUATION — never to the next DATUM.
//! * `rspace.rs::consume` has the same shape: one `extract_data_candidates` pick, one
//!   `check_commit`, and on `false` the continuation is installed and the data left alone.
//!
//! So the outcome is decided entirely by WHICH datum the single pick returns, and that is not
//! stable — fixing the arrival order does not fix it either (see
//! [`guard_rejection_does_not_backtrack_to_the_next_resting_datum`], which holds arrival order
//! constant and still splits 6 : 2 over 8 runs). The stuck state is final rather than early:
//! the store is read at quiescence, with an enabled COMM left unfired and no later produce to
//! re-trigger it. That witness is written to FAIL LOUDLY once the matcher is repaired, so this
//! file and the run sheet get revisited together, while the demo-level beats assert what is
//! true in every run: the vetoed 55 is never consumed and never observed.

#![cfg(feature = "rho-languages")]

use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Stdio};

use mettail_languages::rhocalc::Proc;
use mettail_rholang_runtime::{
    lower_rhocalc_proc, run_normalized_par_for_oracle_and_read_runtime_value_channels,
    run_rholang_source_sequence_for_oracle_and_read_ints,
};
use mettail_runtime::clear_var_cache;

// ════════════════════════════════════════════════════════════════════════════════════════════
// ★ The demo's identity — the ONLY two rename-coupled names in this file
// ════════════════════════════════════════════════════════════════════════════════════════════

/// The demo directory, relative to the workspace root.
const DEMO_DIR: &str = "demos/rhocalc-settlement";

/// The language the run sheet's launch line starts the REPL in (`repl <LANGUAGE>`).
const STARTUP_LANGUAGE: &str = "rhocalc";

// ════════════════════════════════════════════════════════════════════════════════════════════
// The beats, verbatim from RUN-SHEET.md
// ════════════════════════════════════════════════════════════════════════════════════════════

const BEAT_0_INFO: &str = "info";
const BEAT_1_UINT_SUM: &str = "exec 2u32 + 3u32";
const BEAT_1_BARE_SUM: &str = "exec 1 + 2";
const BEAT_1_BIGINT_SUM: &str = "exec 1n + 2n";
const BEAT_2_COMM: &str = r#"exec { for(x <- @("c")){*(x)} | @("c")!(@("OUT")!("p")) }"#;
const BEAT_3_OFFER_PASSES: &str = r#"exec { desk | @("offer")!(42u32) }"#;
const BEAT_3_OFFER_VETOED: &str = r#"exec { desk | @("offer")!(55u32) }"#;
const BEAT_3_TWO_OFFERS: &str = r#"exec { desk | @("offer")!(55u32) | @("offer")!(42u32) }"#;
const BEAT_3B_VACUOUS_GUARD: &str = r#"exec { for(@px <- @("offer") where false implies false){@("OUT")!(px)} | @("offer")!(42u32) }"#;
const BEAT_3B_REFUTED_GUARD: &str = r#"exec { for(@px <- @("offer") where true implies false){@("OUT")!(px)} | @("offer")!(42u32) }"#;
const BEAT_4_SETTLES: &str = r#"exec { settle | @("bid")!(42u32) | @("ask")!(10u32) }"#;
const BEAT_4_OVER_BUDGET: &str = r#"exec { settle | @("bid")!(60u32) | @("ask")!(10u32) }"#;
const BEAT_5_DIVIDE_BY_ZERO: &str =
    r#"exec { for(@q <- @("qty") where 100u32 / q >= 1u32){@("OUT")!(q)} | @("qty")!(0u32) }"#;
const BEAT_5_DIVIDES: &str =
    r#"exec { for(@q <- @("qty") where 100u32 / q >= 1u32){@("OUT")!(q)} | @("qty")!(4u32) }"#;
const BEAT_6_STEP_FIRES: &str = r#"step { desk | @("offer")!(42u32) }"#;
const BEAT_6_STEP_VETOED: &str = r#"step { desk | @("offer")!(55u32) }"#;
const BEAT_7_LIST_METHOD: &str = "exec [1, 2].length()";
const CAMEO_A_LANG: &str = "lang lambda";
const CAMEO_A_STEP: &str = "step --taus (lam x. x, lam a. lam b. a)";
const CAMEO_B_LANG: &str = "lang calculator";
const CAMEO_B_EXEC: &str = "exec 5 / 0";

/// `apply 0` — the Beat-6 advance. Written in the sheet as inline prose rather than in a
/// command fence, so it is driven here but is deliberately absent from [`driven_commands`].
const APPLY_FIRST_EDGE: &str = "apply 0";

/// The desk bindings prelude, exactly as the run sheet's second launch step spells it.
fn load_env_command() -> String {
    format!("load-env {DEMO_DIR}/settlement.env")
}

/// Every command line this file drives that the run sheet also prints in a command fence.
/// [`every_run_sheet_command_line_is_driven_by_this_test`] compares this against the sheet,
/// so a beat added to the sheet without coverage here fails the build.
fn driven_commands() -> Vec<String> {
    let mut commands = vec![load_env_command()];
    commands.extend(
        [
            BEAT_0_INFO,
            BEAT_1_UINT_SUM,
            BEAT_1_BARE_SUM,
            BEAT_1_BIGINT_SUM,
            BEAT_2_COMM,
            BEAT_3_OFFER_PASSES,
            BEAT_3_OFFER_VETOED,
            BEAT_3_TWO_OFFERS,
            BEAT_3B_VACUOUS_GUARD,
            BEAT_3B_REFUTED_GUARD,
            BEAT_4_SETTLES,
            BEAT_4_OVER_BUDGET,
            BEAT_5_DIVIDE_BY_ZERO,
            BEAT_5_DIVIDES,
            BEAT_6_STEP_FIRES,
            BEAT_6_STEP_VETOED,
            BEAT_7_LIST_METHOD,
            CAMEO_A_LANG,
            CAMEO_A_STEP,
            CAMEO_B_LANG,
            CAMEO_B_EXEC,
        ]
        .into_iter()
        .map(str::to_string),
    );
    commands
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// Harness — drive the built REPL exactly as the run sheet's launch line does
// ════════════════════════════════════════════════════════════════════════════════════════════

/// The workspace root: the run sheet's `load-env` path is relative to it, so the REPL must be
/// launched from there (as a presenter would).
fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .canonicalize()
        .expect("the workspace root resolves from the repl manifest directory")
}

/// A file inside the demo directory.
fn demo_file(name: &str) -> PathBuf {
    workspace_root().join(DEMO_DIR).join(name)
}

/// Run the built `repl` binary on `script`, one command per line, and return stdout and
/// stderr concatenated (a typed refusal is printed on stderr; the presenter sees one stream).
///
/// `NO_COLOR` keeps the transcript free of ANSI escapes on every terminal, so the assertions
/// below compare the text the audience reads.
fn run_repl(script: &[&str]) -> String {
    let mut child = Command::new(env!("CARGO_BIN_EXE_repl"))
        .arg(STARTUP_LANGUAGE)
        .current_dir(workspace_root())
        .env("NO_COLOR", "1")
        .env("RUST_MIN_STACK", "8388608")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("the repl binary must start");
    {
        // Taken (not borrowed) so the pipe CLOSES at the end of this block: the REPL's read
        // loop exits on EOF, which is what ends the session.
        let mut stdin = child.stdin.take().expect("the repl reads piped stdin");
        for line in script {
            writeln!(stdin, "{line}").expect("the repl accepts a scripted command line");
        }
    }
    let output = child.wait_with_output().expect("the repl must exit on EOF");
    format!(
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    )
}

/// Run `beats` after loading the desk bindings, as every guard beat requires.
fn run_repl_with_desk(beats: &[&str]) -> String {
    let load = load_env_command();
    let mut script = vec![load.as_str()];
    script.extend_from_slice(beats);
    let transcript = run_repl(&script);
    let loaded = format!("Loaded {} declaration(s)", settlement_env_bindings().len());
    assert!(
        transcript.contains(&loaded),
        "the desk bindings must load before any guard beat runs ({loaded}):\n{transcript}"
    );
    transcript
}

/// The `OUT: […] (n value(s))` lines of a transcript, in order — the line the run sheet
/// quotes as each beat's expected output.
fn out_lines(transcript: &str) -> Vec<String> {
    transcript
        .lines()
        .map(str::trim)
        .filter(|line| line.starts_with("OUT: ["))
        .map(str::to_string)
        .collect()
}

/// Assert `transcript` contains `needle`, printing the whole transcript when it does not.
fn assert_shows(transcript: &str, needle: &str) {
    assert!(
        transcript.contains(needle),
        "expected the transcript to contain {needle:?}\n── transcript ──\n{transcript}"
    );
}

/// Assert `transcript` does NOT contain `needle`.
fn assert_absent(transcript: &str, needle: &str) {
    assert!(
        !transcript.contains(needle),
        "expected the transcript NOT to contain {needle:?}\n── transcript ──\n{transcript}"
    );
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// `settlement.env` — the desk bindings
// ════════════════════════════════════════════════════════════════════════════════════════════

/// Split an env-file line into `(name, term)` the way `Repl::parse_assignment` does: on the
/// first `=` at bracket depth 0, with the left side a plain identifier. Reimplemented rather
/// than imported because it is the REPL's private loader contract this file is validating.
fn split_assignment(line: &str) -> Option<(String, String)> {
    let mut depth = 0i32;
    for (index, character) in line.char_indices() {
        match character {
            '(' | '{' | '[' => depth += 1,
            ')' | '}' | ']' => depth -= 1,
            '=' if depth == 0 => {
                let name = line[..index].trim();
                let term = line[index + 1..].trim();
                let is_identifier = name
                    .chars()
                    .next()
                    .is_some_and(|first| first.is_alphabetic())
                    && name.chars().all(|c| c.is_alphanumeric() || c == '_');
                return (is_identifier && !term.is_empty())
                    .then(|| (name.to_string(), term.to_string()));
            },
            _ => {},
        }
    }
    None
}

/// The demo's env file as `(name, term)` pairs, in file order.
fn settlement_env_bindings() -> Vec<(String, String)> {
    let text = std::fs::read_to_string(demo_file("settlement.env"))
        .expect("the demo ships settlement.env");
    text.lines()
        .map(str::trim)
        .filter(|line| !line.is_empty() && !line.starts_with("//") && !line.starts_with('#'))
        .map(|line| {
            split_assignment(line)
                .unwrap_or_else(|| panic!("settlement.env line is not a binding: {line:?}"))
        })
        .collect()
}

/// The right-hand side of one `settlement.env` binding — the desk process itself, read from
/// the file so the runtime-level beats below run the SHIPPED definition, not a copy of it.
fn desk_binding(name: &str) -> String {
    settlement_env_bindings()
        .into_iter()
        .find(|(bound, _)| bound == name)
        .unwrap_or_else(|| panic!("settlement.env must bind {name:?}"))
        .1
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// Runtime readback — what RESTS, which the REPL's OUT view cannot show
// ════════════════════════════════════════════════════════════════════════════════════════════

/// Run one RhoCalc program to rest and report the values left on each channel, rendered the
/// way the REPL renders an observation (so an expectation reads like the run sheet's).
async fn rest_on_channels(program: &str, channels: &[&str]) -> Vec<(String, Vec<String>)> {
    clear_var_cache();
    let proc = Proc::parse_via_wpda(program)
        .unwrap_or_else(|err| panic!("the demo program must parse: {program:?}: {err:?}"));
    let par = lower_rhocalc_proc(&proc)
        .unwrap_or_else(|err| panic!("the demo program must lower: {program:?}: {err:?}"));
    let observed = run_normalized_par_for_oracle_and_read_runtime_value_channels(&par, channels)
        .await
        .unwrap_or_else(|err| panic!("the demo program must run to rest: {program:?}: {err}"));
    channels
        .iter()
        .map(|channel| {
            let mut rendered: Vec<String> = observed
                .get(*channel)
                .map(|values| values.iter().map(|value| format!("{value}")).collect())
                .unwrap_or_default();
            rendered.sort();
            ((*channel).to_string(), rendered)
        })
        .collect()
}

/// The Beat-3/6 desk program with `offers` in parallel, built from the SHIPPED `desk` binding
/// exactly as the REPL's structure-preserving env substitution builds it.
fn desk_program(offers: &str) -> String {
    format!("{{ {} | {offers} }}", desk_binding("desk"))
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// Beat 0 — orientation
// ════════════════════════════════════════════════════════════════════════════════════════════

/// `info` reports the language's INSTALLED runtime backends. The Rho machine is the default
/// and the only capability the summary names — the run sheet's older "names the two-stage
/// Dovetail+Rholang backend" reading is the WRAPPER's internal shape, which this line has
/// never printed (`runtime_backend_summary` prints capabilities, and RhoCalc advertises one).
#[test]
fn beat_0_info_reports_the_rho_machine_as_the_default_runtime() {
    let transcript = run_repl(&[BEAT_0_INFO]);
    assert_shows(&transcript, "RUNTIME");
    assert_shows(&transcript, "RhoMachine (default)");
    assert_absent(&transcript, "No production runtime wrapper is installed");
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// Beat 1 — even arithmetic is machine work
// ════════════════════════════════════════════════════════════════════════════════════════════

/// Both sums are computed by the machine's metered expression algebra and read back off
/// RSpace. The BARE literal observes as the `Int` `3`, not as big-int bytes: divergence I
/// (`12704fc1`, 2026-07-25) made a numeral's carrier a function of the numeral, so a plain
/// `1` is f1r3node's `GInt` and only the `1n` spelling is `GBigInt`.
#[test]
fn beat_1_arithmetic_is_computed_by_the_machine() {
    let transcript = run_repl(&[BEAT_1_UINT_SUM, BEAT_1_BARE_SUM]);
    assert_eq!(
        out_lines(&transcript),
        vec!["OUT: [5] (1 value(s))", "OUT: [3] (1 value(s))"],
        "both sums rest on OUT as machine-computed values"
    );
    assert_shows(&transcript, "- backend: RhoMachine");
    assert_shows(&transcript, "- artifact: RhoNormalizedAst");
}

/// A numeral's carrier is a function of the NUMERAL: the `n`-less spelling is a `GInt`, the
/// `n`-suffixed one a `GBigInt` whose raw bytes are what rests on the tuplespace. Pinned as a
/// pair because the difference between these two lines is the exact drift the run sheet
/// carried until 2026-07-25, and asserting either alone would not catch a re-merge of the
/// carriers.
#[test]
fn beat_1_the_numeral_spelling_selects_the_wire_carrier() {
    let transcript = run_repl(&[BEAT_1_BARE_SUM, BEAT_1_BIGINT_SUM]);
    assert_eq!(
        out_lines(&transcript),
        vec!["OUT: [3] (1 value(s))", "OUT: [BigInt(0x03)] (1 value(s))"],
        "`1 + 2` rests as a GInt; `1n + 2n` rests as GBigInt bytes"
    );
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// Beat 2 — hello COMM
// ════════════════════════════════════════════════════════════════════════════════════════════

/// A rho-calculus COMM written in RhoCalc executes as a machine COMM: the receiver binds the
/// sent process and drops it, and the `"p"` it publishes rests on OUT.
#[test]
fn beat_2_a_rhocalc_comm_runs_as_a_machine_comm() {
    let transcript = run_repl(&[BEAT_2_COMM]);
    assert_eq!(out_lines(&transcript), vec![r#"OUT: ["p"] (1 value(s))"#]);
    assert_shows(&transcript, "- backend: RhoMachine");
    assert_shows(&transcript, "- artifact: RhoNormalizedAst");
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// Beat 3 — the desk: a guarded limit order
// ════════════════════════════════════════════════════════════════════════════════════════════

/// The two single-offer beats: an offer inside the limit settles, and one over it is vetoed
/// with an EMPTY observation channel — the veto is visible, not silent.
#[test]
fn beat_3_the_guard_admits_the_limit_order_and_vetoes_the_rest() {
    let transcript = run_repl_with_desk(&[BEAT_3_OFFER_PASSES, BEAT_3_OFFER_VETOED]);
    assert_eq!(
        out_lines(&transcript),
        vec!["OUT: [42] (1 value(s))", "OUT: [] (0 value(s))"],
        "42 settles; 55 is vetoed and OUT is observably empty"
    );
}

/// The other half of the veto, which `OUT` alone cannot show: the rejected 55 is still
/// RESTING on `@"offer"`, so nothing was consumed and nothing was fabricated. Read from the
/// same quiescent store as the empty OUT, which is what makes the two facts hold TOGETHER.
#[tokio::test(flavor = "multi_thread")]
async fn beat_3_the_vetoed_offer_is_left_resting_on_the_book() {
    let vetoed = rest_on_channels(&desk_program(r#"@("offer")!(55u32)"#), &["OUT", "offer"]).await;
    assert_eq!(
        vetoed,
        vec![
            ("OUT".to_string(), Vec::<String>::new()),
            ("offer".to_string(), vec!["55".to_string()]),
        ],
        "the failed guard commits nothing and leaves the rejected offer on the book"
    );

    let settled = rest_on_channels(&desk_program(r#"@("offer")!(42u32)"#), &["OUT", "offer"]).await;
    assert_eq!(
        settled,
        vec![
            ("OUT".to_string(), vec!["42".to_string()]),
            ("offer".to_string(), Vec::<String>::new()),
        ],
        "the satisfied guard commits, consuming the offer it settled"
    );
}

/// Beat 3's third command, where the book holds BOTH an admissible and an inadmissible offer.
///
/// ⚠ Defect D1 (module docs): the run sheet claims `OUT: [42] (1 value(s))` — the correct
/// semantics, since a receive with a satisfying datum available is an enabled COMM — but the
/// matcher never backtracks past a guard-rejected datum, so the outcome turns on which of the
/// two offers the single spatial pick returns (12 × `[42]`, 8 × `[]` over 20 hand runs,
/// 2026-07-25). What this test asserts is what holds in EVERY run and is the beat's actual
/// claim about the guard: the 55 is never consumed and never observed. The settling half is
/// asserted deterministically one offer at a time by
/// [`beat_3_the_vetoed_offer_is_left_resting_on_the_book`], and the defect itself by
/// [`guard_rejection_does_not_backtrack_to_the_next_resting_datum`].
#[test]
fn beat_3_the_inadmissible_offer_is_never_the_one_that_settles() {
    let transcript = run_repl_with_desk(&[BEAT_3_TWO_OFFERS]);
    let observed = out_lines(&transcript);
    assert_eq!(observed.len(), 1, "one exec, one observation channel: {observed:?}");
    assert!(
        observed[0] == "OUT: [42] (1 value(s))" || observed[0] == "OUT: [] (0 value(s))",
        "the two-offer book settles the 42 or rests (defect D1) — never anything else: {observed:?}"
    );
    assert_absent(&transcript, "OUT: [55]");
}

/// The resting side of the same beat: whatever the scheduler picks, the 55 is on the book
/// afterwards, and the 42 is on the book exactly when it did not settle. No run consumes the
/// 55, and no run fabricates a value.
#[tokio::test(flavor = "multi_thread")]
async fn beat_3_two_offers_never_consume_the_inadmissible_one() {
    let observed = rest_on_channels(
        &desk_program(r#"@("offer")!(55u32) | @("offer")!(42u32)"#),
        &["OUT", "offer"],
    )
    .await;
    let out = &observed[0].1;
    let offer = &observed[1].1;
    assert!(
        out.as_slice() == ["42".to_string()] || out.is_empty(),
        "the guarded receive settles the 42 or rests (defect D1): {observed:?}"
    );
    assert!(offer.contains(&"55".to_string()), "the 55 is never consumed: {observed:?}");
    let expected_offer: Vec<String> = match out.is_empty() {
        true => vec!["42".to_string(), "55".to_string()],
        false => vec!["55".to_string()],
    };
    assert_eq!(
        offer, &expected_offer,
        "the book holds exactly what did not settle: {observed:?}"
    );
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// Beat 3b — the guard the machine never sees
// ════════════════════════════════════════════════════════════════════════════════════════════

/// A binder-closed guard is decided at lowering time: `false implies false` is vacuously true
/// and the receive commits; `true implies false` is refuted, is REPORTED rather than removed,
/// and the receive never fires. (`guard_discharge_corpus.rs` asserts the artifact-level half
/// — condition absent vs. present; this asserts the beat as the audience sees it.)
#[test]
fn beat_3b_the_vacuous_guard_commits_and_the_refuted_one_never_does() {
    let transcript = run_repl(&[BEAT_3B_VACUOUS_GUARD, BEAT_3B_REFUTED_GUARD]);
    assert_eq!(
        out_lines(&transcript),
        vec!["OUT: [42] (1 value(s))", "OUT: [] (0 value(s))"],
        "F ⇒ F is vacuously true and commits; T ⇒ F can never fire"
    );
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// Beat 4 — atomic cross-channel settlement
// ════════════════════════════════════════════════════════════════════════════════════════════

/// The `&`-join consumes both legs atomically and the machine's `EMult` computes the product;
/// over budget, the whole trade is refused.
#[test]
fn beat_4_the_cross_channel_join_settles_or_refuses_atomically() {
    let transcript = run_repl_with_desk(&[BEAT_4_SETTLES, BEAT_4_OVER_BUDGET]);
    assert_eq!(
        out_lines(&transcript),
        vec!["OUT: [420] (1 value(s))", "OUT: [] (0 value(s))"],
        "42 × 10 = 420 settles; 60 × 10 = 600 exceeds the 500 budget"
    );
}

/// The all-or-nothing half: when the cross-bind guard fails, NEITHER leg is consumed — both
/// the bid and the ask are still resting. The single-channel OUT view cannot state this.
#[tokio::test(flavor = "multi_thread")]
async fn beat_4_an_over_budget_trade_leaves_both_legs_resting() {
    let program =
        format!(r#"{{ {} | @("bid")!(60u32) | @("ask")!(10u32) }}"#, desk_binding("settle"));
    assert_eq!(
        rest_on_channels(&program, &["OUT", "bid", "ask"]).await,
        vec![
            ("OUT".to_string(), Vec::<String>::new()),
            ("bid".to_string(), vec!["60".to_string()]),
            ("ask".to_string(), vec!["10".to_string()]),
        ],
        "a violated budget consumes neither leg — transactional matching, zero partial effects"
    );

    let settling =
        format!(r#"{{ {} | @("bid")!(42u32) | @("ask")!(10u32) }}"#, desk_binding("settle"));
    assert_eq!(
        rest_on_channels(&settling, &["OUT", "bid", "ask"]).await,
        vec![
            ("OUT".to_string(), vec!["420".to_string()]),
            ("bid".to_string(), Vec::<String>::new()),
            ("ask".to_string(), Vec::<String>::new()),
        ],
        "the admitted trade consumes both legs and publishes the product"
    );
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// Beat 5 — SafeArith as a veto
// ════════════════════════════════════════════════════════════════════════════════════════════

/// A partial operation inside the guard fails CLOSED: `100 / 0` makes the rewrite impossible
/// rather than raising; a divisor that divides settles normally.
#[test]
fn beat_5_division_by_zero_inside_a_guard_is_a_veto_not_a_crash() {
    let transcript = run_repl(&[BEAT_5_DIVIDE_BY_ZERO, BEAT_5_DIVIDES]);
    assert_eq!(
        out_lines(&transcript),
        vec!["OUT: [] (0 value(s))", "OUT: [4] (1 value(s))"],
        "DivisionByZero in the pure guard evaluator is a guard-fail; 100 / 4 ≥ 1 commits"
    );
    assert_absent(&transcript, "panicked");
}

/// …and the undividable datum is still on its channel afterwards.
#[tokio::test(flavor = "multi_thread")]
async fn beat_5_the_undividable_datum_is_left_resting() {
    let program =
        r#"{ for(@q <- @("qty") where 100u32 / q >= 1u32){@("OUT")!(q)} | @("qty")!(0u32) }"#;
    assert_eq!(
        rest_on_channels(program, &["OUT", "qty"]).await,
        vec![
            ("OUT".to_string(), Vec::<String>::new()),
            ("qty".to_string(), vec!["0".to_string()]),
        ],
        "the unsafe computation vetoes the COMM and leaves the datum available"
    );
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// Beat 6 — the live COMM trace
// ════════════════════════════════════════════════════════════════════════════════════════════

/// The Layer-2 reactive stepper wraps the real RSpace: the trace is exactly two steps — the
/// committed COMM that consumes the 42 with its continuation, then the output that observes
/// it — and `apply 0` advances from the first to the second.
#[test]
fn beat_6_the_step_trace_shows_the_committed_comm_then_the_output() {
    let transcript = run_repl_with_desk(&[BEAT_6_STEP_FIRES, APPLY_FIRST_EDGE]);
    assert_shows(&transcript, "- backend: RhoMachine");
    assert_shows(&transcript, "- 2 reduction step(s) on the Rho machine");
    assert_shows(&transcript, "Reduction trace (step 0):");
    assert_shows(&transcript, r#"[Rho COMM] COMM[consume] "offer" ⇐"#);
    assert_shows(&transcript, "{ 42 }");
    assert_shows(&transcript, r#"▸ cont "OUT"!(x-1)"#);
    assert_shows(&transcript, "Use apply 0 to advance to the next reduction (1 remaining).");
    assert_shows(&transcript, "Applied graph edge → output");
    assert_shows(&transcript, "[Rho output] OUT observes 42");
}

/// The vetoed offer commits NOTHING, so there is no COMM to trace: the router falls back to
/// the Layer-1 Dovetail graph, which has no rewrite from this term. A live recorder watching
/// real RSpace saw zero committed COMMs while the predicate ran.
#[test]
fn beat_6_a_vetoed_guard_produces_no_committed_comm_at_all() {
    let transcript = run_repl_with_desk(&[BEAT_6_STEP_VETOED]);
    assert_shows(&transcript, "- backend: Dovetail");
    assert_shows(&transcript, "- 0 rewrite edge(s)");
    assert_shows(&transcript, "No rewrites from this term (already a normal form).");
    assert_absent(&transcript, "[Rho COMM]");
    assert_absent(&transcript, "reduction step(s) on the Rho machine");
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// Beat 7 — the universal mandate, fail-closed
// ════════════════════════════════════════════════════════════════════════════════════════════

/// A construct the machine cannot run is a TYPED refusal naming the construct — never a
/// silent host-side fold.
#[test]
fn beat_7_a_construct_the_machine_cannot_run_is_a_typed_refusal() {
    let transcript = run_repl(&[BEAT_7_LIST_METHOD]);
    assert_shows(
        &transcript,
        "could not be lowered to the Rho machine (A-S4 fail-closed lowering; \
         no host fold-normalization fallback)",
    );
    assert_shows(&transcript, r#"UnsupportedProc("l.length() list method")"#);
    assert_absent(&transcript, "OUT: [");
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// Cameos
// ════════════════════════════════════════════════════════════════════════════════════════════

/// Cameo A. `step` prefers the Layer-1 Dovetail rewrite graph whenever the term HAS a
/// structural successor, and a β-redex has one — so this subject shows the rewrite graph and
/// `apply 0` performs the β step. It shows no `[τ …]` node: τ classification covers the
/// in-Rho DRIVE families (`^drive` / `^subst` / `^drive-ac` / `^float`), which a `step` trace
/// does not ride today (the F5 pin in `rholang-runtime/src/step.rs`). Asserted so the cameo
/// cannot silently start or stop showing τ machinery.
#[test]
fn cameo_a_the_beta_redex_steps_through_the_layer_1_rewrite_graph() {
    let transcript = run_repl(&[CAMEO_A_LANG, CAMEO_A_STEP, APPLY_FIRST_EDGE]);
    assert_shows(&transcript, "- backend: Dovetail");
    assert_shows(&transcript, "- 1 rewrite edge(s)");
    assert_shows(&transcript, "Use apply 0 to apply a rewrite (1 available).");
    assert_shows(&transcript, "lam _ . lam _ . a");
    assert_absent(&transcript, "[τ ");
}

/// Cameo B. A semantic-predicate deferral is today's only non-Rho-machine runtime site: the
/// blocked Calculator division lazily builds the Dovetail report and returns it.
#[test]
fn cameo_b_the_predicate_deferral_is_the_only_non_machine_runtime_site() {
    let transcript = run_repl(&[CAMEO_B_LANG, CAMEO_B_EXEC]);
    assert_shows(&transcript, "- backend: Dovetail");
    assert_shows(&transcript, "- artifact: DovetailRunReport");
    assert_shows(&transcript, "Calculator::Int::DivInt");
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// Script integrity — the sheet and the env file cannot drift from this test
// ════════════════════════════════════════════════════════════════════════════════════════════

/// Every `Prompt> command` line printed in a fenced block of `RUN-SHEET.md`.
fn run_sheet_commands() -> Vec<String> {
    let sheet =
        std::fs::read_to_string(demo_file("RUN-SHEET.md")).expect("the demo ships a RUN-SHEET.md");
    let mut inside_fence = false;
    let mut commands = Vec::new();
    for line in sheet.lines() {
        if line.trim_start().starts_with("```") {
            inside_fence = !inside_fence;
            continue;
        }
        if !inside_fence {
            continue;
        }
        let Some((prompt, command)) = line.trim().split_once("> ") else {
            continue;
        };
        let is_prompt = !prompt.is_empty() && prompt.chars().all(|c| c.is_ascii_alphanumeric());
        if is_prompt && !command.trim().is_empty() {
            commands.push(command.trim().to_string());
        }
    }
    commands
}

/// The run sheet's command lines and the lines this file drives are the SAME set. A beat added
/// to the sheet without coverage, or a beat whose spelling drifts, fails here — which is what
/// makes the sheet an executed script rather than a narrative.
#[test]
fn every_run_sheet_command_line_is_driven_by_this_test() {
    let mut from_sheet = run_sheet_commands();
    let mut driven = driven_commands();
    from_sheet.sort();
    driven.sort();
    assert_eq!(
        from_sheet, driven,
        "RUN-SHEET.md's command lines must be exactly the lines this test drives \
         (left = sheet, right = driven)"
    );
}

/// The launch line names the binary and startup language this test actually drives, so the
/// pending `repl rhocalc` → `repl rholang` rename cannot land in one place only.
#[test]
fn the_run_sheet_launch_line_matches_the_binary_this_test_drives() {
    let sheet =
        std::fs::read_to_string(demo_file("RUN-SHEET.md")).expect("the demo ships a RUN-SHEET.md");
    let launch = sheet
        .lines()
        .map(str::trim)
        .find(|line| line.starts_with("$ ") && line.contains("repl"))
        .expect("the run sheet prints a launch line");
    assert!(
        launch.ends_with(&format!("repl {STARTUP_LANGUAGE}")),
        "the launch line must start the REPL in {STARTUP_LANGUAGE:?}: {launch:?}"
    );
    assert!(
        launch.contains("target/"),
        "the launch line must name a built binary: {launch:?}"
    );
}

/// Every line of `settlement.env` loads, and every name it binds is USED by the run sheet —
/// no dead bindings, and no beat referring to a binding the file does not ship.
#[test]
fn settlement_env_binds_exactly_the_names_the_run_sheet_uses() {
    let bindings = settlement_env_bindings();
    let bound: Vec<&str> = bindings.iter().map(|(name, _)| name.as_str()).collect();
    assert_eq!(bound, vec!["desk", "settle"], "the demo ships exactly the two desk bindings");

    let commands = run_sheet_commands().join("\n");
    for (name, term) in &bindings {
        assert!(
            commands.split_whitespace().any(|word| word == name),
            "settlement.env binds {name:?} ({term:?}) but no run-sheet command uses it"
        );
    }

    // …and the REPL loads every one of them, counting the file's lines, not its bindings.
    let load = load_env_command();
    let transcript = run_repl(&[load.as_str(), "env"]);
    assert_shows(&transcript, &format!("Loaded {} declaration(s)", bindings.len()));
    for (name, _) in &bindings {
        assert_shows(&transcript, &format!("{name} = for("));
    }
}

/// The guards this demo ships parse and lower as written. The `<=` in `desk` is also the
/// PERSISTENT-BIND arrow (`for(x <= chan)`), and the `*` in `settle` is also the drop prefix,
/// so both bindings sit on genuine grammar ambiguities; the run sheet offers `<`-spelled
/// fallbacks in case they ever stop parsing. This asserts the shipped spellings work, so the
/// fallbacks stay a contingency rather than becoming the demo.
#[test]
fn the_shipped_guard_spellings_parse_and_lower() {
    for (name, term) in settlement_env_bindings() {
        clear_var_cache();
        let proc = Proc::parse_via_wpda(&term)
            .unwrap_or_else(|err| panic!("settlement.env {name} must parse: {term:?}: {err:?}"));
        lower_rhocalc_proc(&proc)
            .unwrap_or_else(|err| panic!("settlement.env {name} must lower: {term:?}: {err:?}"));
    }
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// ⚠ Defect D1 — pinned deterministically
// ════════════════════════════════════════════════════════════════════════════════════════════

/// ⚠ The witness for defect D1 (module docs): a `where`-guard rejection does not backtrack to
/// the next resting datum, so an ENABLED rendezvous can be permanently unreachable.
///
/// **The fixed program.** Two data rest on `@"offer"` — a 55 the guard rejects and a 42 it
/// admits — and only then is the guarded receive installed. There is no later produce to
/// re-trigger the rendezvous, so whatever the consume decides is final: the store is read at
/// quiescence. The 42 satisfies the guard in EVERY run, so the COMM is enabled in every run
/// and `OUT == [42]`, `offer == [55]` is the only outcome the semantics admit.
///
/// **Why this is a repetition experiment rather than a single assertion.** The consume takes
/// exactly ONE spatial pick (`find_matching_data_candidate` — the guard is not consulted),
/// evaluates the guard once (`check_commit`), and on rejection abandons the attempt. WHICH of
/// the two resting data it picks is not stable even with arrival order fixed: over 8
/// consecutive runs (2026-07-25) this exact program rested 6 times and committed 2 times. So
/// the defect is stated the only way it is true — the stuck state is REACHABLE — and both
/// outcomes are required to appear, which together prove the run-to-run split rather than a
/// uniformly-broken or uniformly-working matcher.
///
/// **Canary.** When the matcher backtracks past a guard-rejected datum, no run rests and this
/// test FAILS on its `rested > 0` assertion — deliberately, so this file, the run sheet's
/// Beat 3, and [`beat_3_the_inadmissible_offer_is_never_the_one_that_settles`] are revisited
/// together. With `p(rest) ≈ 0.75` per trial the 24 trials below make a false failure
/// (~`0.25^24`) unreachable in practice.
#[tokio::test(flavor = "multi_thread")]
async fn guard_rejection_does_not_backtrack_to_the_next_resting_datum() {
    /// The desk's guard and offers, transliterated to Rholang: the defect lives in the SHARED
    /// matcher, so the witness is written at the layer that reaches it most directly.
    const GUARDED_RECEIVE: &str = r#"for (@px <- @"offer" where px <= 45) { @"OUT"!(px) }"#;
    const ADMISSIBLE: &str = r#"@"offer"!(42)"#;
    const REJECTED: &str = r#"@"offer"!(55)"#;
    /// Trials of the same fixed program. See the canary note for the sizing argument.
    const TRIALS: usize = 24;

    let mut committed = 0usize;
    let mut rested = 0usize;
    for trial in 0..TRIALS {
        // Each producer is its own evaluation, so both data are resting BEFORE the guarded
        // receive is installed — the consume path this defect is about.
        let observed = run_rholang_source_sequence_for_oracle_and_read_ints(
            &[ADMISSIBLE, REJECTED, GUARDED_RECEIVE],
            &["OUT", "offer"],
        )
        .await
        .expect("the guarded receive sequence runs");
        let mut out = observed.get("OUT").cloned().unwrap_or_default();
        let mut book = observed.get("offer").cloned().unwrap_or_default();
        out.sort();
        book.sort();
        match (out.as_slice(), book.as_slice()) {
            // The semantics: the admissible datum settles, the rejected one stays on the book.
            ([42], [55]) => committed += 1,
            // ⚠ D1: the guard rejected the pick and the consume never tried the other datum.
            ([], [42, 55]) => rested += 1,
            other => panic!(
                "trial {trial}: a guarded consume may only settle the 42 or rest — it may \
                 never consume the 55 and never fabricate a value: {other:?}"
            ),
        }
    }

    assert!(
        rested > 0,
        "⚠ DEFECT D1 appears to be FIXED: {TRIALS}/{TRIALS} trials settled the enabled COMM. \
         That is the correct semantics — so tighten this test to require it, restore Beat 3's \
         unqualified `OUT: [42] (1 value(s))` in demos/rhocalc-settlement/RUN-SHEET.md, and \
         tighten beat_3_the_inadmissible_offer_is_never_the_one_that_settles"
    );
    assert!(
        committed > 0,
        "the rendezvous must be REACHABLE — {TRIALS}/{TRIALS} trials rested, which would mean \
         the guarded consume never commits at all rather than picking nondeterministically \
         (a different, larger defect than D1)"
    );
}
