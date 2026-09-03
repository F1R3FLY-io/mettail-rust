//! CI gate for the **Foreign Assay Desk** demo (`demos/flt-assay-desk/`).
//!
//! The demo's vehicle is the `rholang` interpreter binary run on committed `.rho` files, so this
//! file drives that binary with the run sheet's own command lines and asserts, per beat, what the
//! audience sees. Without it the run sheet is a hand-run narrative that rots silently.
//!
//! ## What is covered, and by which layer
//!
//! | layer | vehicle | answers |
//! |---|---|---|
//! | interpreter transcript | `CARGO_BIN_EXE_rholang` on the committed `.rho` files | what the AUDIENCE sees: the normal form, the `^fired` ledger, the accepted result, the empty OUT |
//! | runtime readback | `lower_rholang_proc_with_resolver` + multi-channel `get_data` | what RESTS — the two REJECTED results still on `@"assay"`, which the interpreter's single-channel `@"OUT"` view cannot show |
//! | script integrity | `RUN-SHEET.md` parsing | every command line in the sheet is driven here |
//! | determinism | repeated identical runs | the presenter's transcript is reproducible, not a lucky schedule |
//!
//! The layers are complementary. "The desk accepted the constant combinator" is one line on
//! `@"OUT"`; "and the two it refused are still on the book" is only observable by reading a
//! SECOND channel of the SAME quiescent store (the `settlement_demo::rest_on_channels`
//! discipline, which this file follows).
//!
//! ## Why four desks and not one
//!
//! A `where` guard exercised over a SINGLE candidate proves nothing: it passes whether or not
//! filtering works. The demo therefore offers the same three resting results to three different
//! predicates, and a fourth desk offers Beat 3's predicate a DIFFERENT datum. This file asserts
//! all four outcomes, and no single defect produces all four:
//!
//! * a **vacuous** guard (one that admits everything) would settle a result in
//!   `desk-accepts-nothing.rho` too;
//! * a **fail-closed** guard (one the substrate cannot decide, silently refusing) would settle
//!   nothing in `desk-accepts-constant.rho` or `desk-accepts-identity.rho`;
//! * a guard that tested only the FIRST resting datum and gave up could not return two DIFFERENT
//!   answers from one unchanged set — which is exactly the pre-2026-07-26 defect D1
//!   (f1r3node-rust-mettail `6bc58743` / `5d37f67e`; see `repl/tests/settlement_demo.rs` for the
//!   full account). This demo is a live regression guard for that repair;
//! * a guard comparing SOURCE TEXT, or matching loosely on the guest-term envelope rather than
//!   on the term, would accept `desk-refuses-the-unreduced-arrival.rho`'s datum — Contract C in
//!   the form it ARRIVES in, whose normal form is the very term the guard names. That desk is
//!   also what makes the run-to-completion load-bearing rather than decorative: take the
//!   reduction away and the same desk, with the same guard, settles nothing.
//!
//! ## Format-agnostic resting assertions
//!
//! The resting-datum assertions never hard-code a rendering of a reflected λ-term. Each expected
//! result is obtained by [`resting_display_of`], which publishes that ONE guest term with no
//! receive at all and reads back what rests — so the expectation is minted by the same reflection
//! path as the datum under test, and a change to the reflected wire format cannot make these
//! tests pass vacuously or fail spuriously.
#![cfg(all(feature = "rholang-runtime", feature = "lambda-runtime"))]

use std::path::PathBuf;
use std::process::{Command, Output};
use std::sync::Arc;

use mettail_languages::lambda::LambdaLanguage;
use mettail_languages::rholang::Proc;
use mettail_rholang_codegen::{FltRegistry, FltResolve};
use mettail_rholang_runtime::{
    lower_rholang_proc_with_resolver, run_normalized_par_for_oracle_and_read_runtime_value_channels,
};
use mettail_runtime::clear_var_cache;

// ════════════════════════════════════════════════════════════════════════════════════════════
// The demo's identity, and the beats verbatim from RUN-SHEET.md
// ════════════════════════════════════════════════════════════════════════════════════════════

/// The demo directory, relative to the workspace root.
const DEMO_DIR: &str = "demos/flt-assay-desk";

/// The build line the run sheet tells the presenter to run. Asserted against the features the
/// `rholang` bin target actually requires, so the sheet cannot tell a presenter to build
/// something that will not produce this test's binary.
const BUILD_COMMAND: &str =
    "cargo build -p rholang-runtime --bin rholang --features \"rholang-runtime lambda-runtime calculator-runtime\"";

const BEAT_1_SHOW_A: &str = "tail -1 demos/flt-assay-desk/contract-a.rho";
const BEAT_1_RUN_A: &str = "target/debug/rholang demos/flt-assay-desk/contract-a.rho";
const BEAT_2_RUN_B: &str = "target/debug/rholang demos/flt-assay-desk/contract-b.rho";
const BEAT_2_RUN_C: &str = "target/debug/rholang demos/flt-assay-desk/contract-c.rho";
const BEAT_3_SHOW_DESK: &str = "tail -7 demos/flt-assay-desk/desk-accepts-constant.rho";
const BEAT_3_RUN_DESK: &str = "target/debug/rholang demos/flt-assay-desk/desk-accepts-constant.rho";
const BEAT_4_RUN_DESK: &str = "target/debug/rholang demos/flt-assay-desk/desk-accepts-identity.rho";
const BEAT_5A_RUN_DESK: &str =
    "target/debug/rholang demos/flt-assay-desk/desk-refuses-the-unreduced-arrival.rho";
const BEAT_5_RUN_DESK: &str = "target/debug/rholang demos/flt-assay-desk/desk-accepts-nothing.rho";

/// Contract C **as it arrives**: the application `(I K)`, whose normal form is the constant
/// combinator but which is not itself the constant combinator.
const UNREDUCED_ARRIVAL: &str = "(lam x. x, lam a. lam b. a)";

/// Every command line this file drives, in sheet order.
/// [`every_run_sheet_command_line_is_driven_by_this_test`] compares this against the sheet, so a
/// beat added to the sheet without coverage here fails the build.
fn driven_commands() -> Vec<String> {
    [
        BUILD_COMMAND,
        BEAT_1_SHOW_A,
        BEAT_1_RUN_A,
        BEAT_2_RUN_B,
        BEAT_2_RUN_C,
        BEAT_3_SHOW_DESK,
        BEAT_3_RUN_DESK,
        BEAT_4_RUN_DESK,
        BEAT_5A_RUN_DESK,
        BEAT_5_RUN_DESK,
    ]
    .into_iter()
    .map(str::to_string)
    .collect()
}

// ── the three guest terms whose normal forms the desk filters over ──────────────────────────

/// The identity combinator `I` — `contract-a.rho`'s normal form.
const NF_IDENTITY: &str = "lam x. x";
/// The mirror combinator `C` (keep the second argument) — `contract-b.rho`'s normal form.
const NF_MIRROR: &str = "lam a. lam b. b";
/// The constant combinator `K` (keep the first argument) — `contract-c.rho`'s normal form.
const NF_CONSTANT: &str = "lam a. lam b. a";

// ════════════════════════════════════════════════════════════════════════════════════════════
// Harness — run the built interpreter exactly as the presenter does
// ════════════════════════════════════════════════════════════════════════════════════════════

/// The workspace root. The run sheet's paths are relative to it, so the interpreter must be
/// launched from there (as a presenter would).
fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .canonicalize()
        .expect("the workspace root resolves from the rholang-runtime manifest directory")
}

/// A file inside the demo directory.
fn demo_file(name: &str) -> PathBuf {
    workspace_root().join(DEMO_DIR).join(name)
}

/// Run the built `rholang` binary on a demo file from the workspace root, capturing its output.
fn run_interpreter(demo: &str) -> Output {
    Command::new(env!("CARGO_BIN_EXE_rholang"))
        .arg(format!("{DEMO_DIR}/{demo}"))
        .current_dir(workspace_root())
        .env_remove("RUST_MIN_STACK")
        .output()
        .expect("the rholang binary must run")
}

/// The interpreter's stdout for a demo file, with a non-zero exit reported as a failure that
/// names both streams (a stuck drive and a lowering refusal are otherwise invisible).
fn transcript(demo: &str) -> String {
    let output = run_interpreter(demo);
    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "rholang exited non-zero on {demo}\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    stdout
}

/// The `@"OUT"` observation lines of a transcript, in the order the interpreter printed them,
/// with the `    [i] ` prefix stripped — e.g. `⟦λ.λ.1⟧`.
///
/// Matching whole observation lines (rather than searching stdout for a needle) is deliberate:
/// `λ.0` is a substring of `λ.λ.0`, and a substring search over the raw transcript would also
/// hit the demo file's own comments, which the interpreter never prints but a future `--emit-
/// comments` beat would. The `⟦…⟧` delimiters plus whole-line extraction make each result
/// unambiguous.
fn out_observations(transcript: &str) -> Vec<String> {
    transcript
        .lines()
        .filter_map(|line| {
            let trimmed = line.trim_start();
            let rest = trimmed.strip_prefix('[')?;
            let (_index, value) = rest.split_once("] ")?;
            Some(value.trim().to_string())
        })
        .collect()
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// Runtime readback — what RESTS, which the interpreter's @"OUT" view cannot show
// ════════════════════════════════════════════════════════════════════════════════════════════

/// The guest registry the interpreter installs, rebuilt identically here so the lowering this
/// file performs is the lowering the demo runs under.
fn guest_resolver() -> Arc<dyn FltResolve> {
    Arc::new(FltRegistry::new().with_guest("lambda", Box::new(LambdaLanguage)))
}

/// Run one Rholang program to rest and report, per channel, the sorted renderings of every datum
/// left on it — all read from ONE quiescent store, which is what makes "the desk settled X" and
/// "and it refused Y, which is still resting" a statement about the same execution rather than
/// two unrelated runs.
async fn rest_on_channels(program: &str, channels: &[&str]) -> Vec<(String, Vec<String>)> {
    clear_var_cache();
    let proc = Proc::parse_via_wpda(program)
        .unwrap_or_else(|err| panic!("the demo program must parse: {err:?}"));
    let par = lower_rholang_proc_with_resolver(&proc, guest_resolver())
        .unwrap_or_else(|err| panic!("the demo program must lower: {err:?}"));
    let observed = run_normalized_par_for_oracle_and_read_runtime_value_channels(&par, channels)
        .await
        .unwrap_or_else(|err| panic!("the demo program must run to rest: {err}"));
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

/// Run one of the committed demo `.rho` files (source verbatim, comments and all) through the
/// same parse+lower path the interpreter uses, and report what rests on `channels`.
async fn rest_on_channels_of_demo(demo: &str, channels: &[&str]) -> Vec<(String, Vec<String>)> {
    let source = std::fs::read_to_string(demo_file(demo))
        .unwrap_or_else(|err| panic!("the demo ships {demo}: {err}"));
    rest_on_channels(&source, channels).await
}

/// The rendering of ONE reflected guest term as it rests on a channel — minted by publishing it
/// with no receiver at all, so the expected value comes from the same reflection path as the
/// value under test. Nothing about the reflected wire format is hard-coded anywhere in this file.
async fn resting_display_of(guest_term: &str) -> String {
    let program = format!("@\"assay\"!(lambda:Term`{guest_term}`)");
    let resting = rest_on_channels(&program, &["assay"]).await;
    let (_channel, values) = resting
        .into_iter()
        .next()
        .expect("one channel was requested");
    assert_eq!(
        values.len(),
        1,
        "publishing one guest term with no receiver must leave exactly one datum resting"
    );
    values.into_iter().next().expect("exactly one datum")
}

/// The three normal forms, sorted, as they rest — the full set the desk filters over.
async fn all_three_results() -> Vec<String> {
    let mut all = vec![
        resting_display_of(NF_IDENTITY).await,
        resting_display_of(NF_MIRROR).await,
        resting_display_of(NF_CONSTANT).await,
    ];
    all.sort();
    all
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// Beats 1 & 2 — three foreign terms driven to normal form BY THE MACHINE
// ════════════════════════════════════════════════════════════════════════════════════════════

/// Beat 1's hook: the last line of `contract-a.rho` is the foreign term as written. The sheet
/// prints it with `tail -1`, so what the audience reads is the committed source.
#[test]
fn beat_1_the_foreign_term_as_written_is_the_last_line_of_the_contract() {
    let source = std::fs::read_to_string(demo_file("contract-a.rho"))
        .expect("the demo ships contract-a.rho");
    assert_eq!(
        source.lines().last().expect("contract-a.rho is non-empty"),
        "lambda:Term`((lam a. lam b. a, lam x. x), lam a. lam b. a)`",
        "the term the sheet shows with `tail -1` is the term the interpreter runs"
    );
}

/// Beat 1. `(K I) K` β-reduces on the reducer to the identity — two firings, by quiescence.
#[test]
fn beat_1_contract_a_drives_to_the_identity_in_two_beta_firings() {
    let stdout = transcript("contract-a.rho");
    assert_eq!(
        out_observations(&stdout),
        vec!["⟦λ.0⟧"],
        "(K I) K must rest at the identity I = λ.0 — K kept its first argument"
    );
    assert!(
        stdout.contains("^fired ledger: [\"Beta\", \"Beta\"]   (2 in-Rho rewrite firing(s))"),
        "the machine's own receipt must show the two Beta firings\nstdout:\n{stdout}"
    );
    assert!(
        stdout.contains(
            "^drive-err: 0 datum(a) · ^drive-fuel: 0 datum(a)   (both empty ⟹ terminated by quiescence)"
        ),
        "it must terminate by QUIESCENCE, not by fuel exhaustion or a typed error\nstdout:\n{stdout}"
    );
    assert!(
        stdout.contains("mode: term → reducing to normal form on the f1r3node reducer"),
        "a bare FLT must take the DRIVE path, not the run-to-rest path\nstdout:\n{stdout}"
    );
}

/// Beat 2. The mirror image `(C I) C` costs the same two firings and lands somewhere else.
#[test]
fn beat_2_contract_b_drives_to_the_mirror_combinator() {
    let stdout = transcript("contract-b.rho");
    assert_eq!(
        out_observations(&stdout),
        vec!["⟦λ.λ.0⟧"],
        "(C I) C must rest at C = λ.λ.0 — C kept its SECOND argument"
    );
    assert!(
        stdout.contains("^fired ledger: [\"Beta\", \"Beta\"]   (2 in-Rho rewrite firing(s))"),
        "two Beta firings, the same cost as contract A\nstdout:\n{stdout}"
    );
}

/// Beat 2. `I K` costs ONE firing — and, crucially, only BECOMES the constant combinator by
/// reducing: what arrives is an application, not a λ. That is why the desk's predicate over the
/// RESULT cannot be satisfied without the reduction having actually happened.
#[test]
fn beat_2_contract_c_drives_to_the_constant_combinator_in_one_firing() {
    let stdout = transcript("contract-c.rho");
    assert_eq!(out_observations(&stdout), vec!["⟦λ.λ.1⟧"], "I K must rest at K = λ.λ.1");
    assert!(
        stdout.contains("^fired ledger: [\"Beta\"]   (1 in-Rho rewrite firing(s))"),
        "exactly one Beta firing\nstdout:\n{stdout}"
    );
    assert!(
        !stdout.contains("⟦(λ.0 λ.λ.1)⟧"),
        "the term must be REDUCED, not echoed as the un-reduced application\nstdout:\n{stdout}"
    );
}

/// The three contracts land on three DISTINCT normal forms. If two coincided, the desk's filter
/// could select the right rendering for the wrong reason.
#[test]
fn the_three_contracts_have_three_distinct_normal_forms() {
    let mut forms = [
        out_observations(&transcript("contract-a.rho")),
        out_observations(&transcript("contract-b.rho")),
        out_observations(&transcript("contract-c.rho")),
    ]
    .concat();
    assert_eq!(forms, vec!["⟦λ.0⟧", "⟦λ.λ.0⟧", "⟦λ.λ.1⟧"]);
    forms.sort();
    forms.dedup();
    assert_eq!(forms.len(), 3, "the three results must be pairwise distinct");
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// The bridge — the desk's payloads ARE the contracts' results, machine-checked
// ════════════════════════════════════════════════════════════════════════════════════════════

/// The desk files publish the three normal forms as literals, because an FLT embedded in a
/// PROCESS is inert today (see the run sheet's scope notes). That hand-off is the one place the
/// demo could silently rot, so it is checked rather than assumed, in two halves.
///
/// **Half one, here**: each payload, run as a BARE term through the same interpreter, reduces to
/// the same normal form the corresponding contract reduced to — with an EMPTY `^fired` ledger,
/// which is the statement that it is already normal. So payload and contract result denote the
/// same $λ$-term, checked by the reducer rather than by string equality on the source.
///
/// **Half two**: [`the_desk_files_publish_exactly_those_three_payloads`] ties the guest sources
/// used here to the ones the committed desk files actually send.
#[test]
fn each_desk_payload_is_the_normal_form_its_contract_reduced_to() {
    let scratch = std::env::temp_dir().join(format!(
        "assay-desk-payload-probe-{}-{:?}.rho",
        std::process::id(),
        std::thread::current().id()
    ));
    for (payload, contract, expected) in [
        (NF_IDENTITY, "contract-a.rho", "⟦λ.0⟧"),
        (NF_MIRROR, "contract-b.rho", "⟦λ.λ.0⟧"),
        (NF_CONSTANT, "contract-c.rho", "⟦λ.λ.1⟧"),
    ] {
        std::fs::write(&scratch, format!("lambda:Term`{payload}`\n"))
            .expect("the probe term must be writable to a temporary file");
        let output = Command::new(env!("CARGO_BIN_EXE_rholang"))
            .arg(&scratch)
            .env_remove("RUST_MIN_STACK")
            .output()
            .expect("the rholang binary must run");
        let stdout = String::from_utf8_lossy(&output.stdout).to_string();
        assert!(output.status.success(), "the probe term must evaluate\nstdout:\n{stdout}");
        assert_eq!(
            out_observations(&stdout),
            vec![expected],
            "the desk's payload `{payload}` must denote the same term {contract} reduced to"
        );
        assert!(
            stdout.contains("^fired ledger: []   (0 in-Rho rewrite firing(s))"),
            "a payload is already a NORMAL FORM, so driving it must fire nothing\nstdout:\n{stdout}"
        );
        assert_eq!(
            out_observations(&transcript(contract)),
            vec![expected],
            "…and that is exactly what {contract} reduces to"
        );
    }
    let _ = std::fs::remove_file(&scratch);
}

/// The other half of the bridge: every desk file sends exactly the three payloads checked above,
/// on `@"assay"`, so the probe terms cannot drift from the demo's actual data.
#[test]
fn the_desk_files_publish_exactly_those_three_payloads() {
    for desk in [
        "desk-accepts-constant.rho",
        "desk-accepts-identity.rho",
        "desk-accepts-nothing.rho",
    ] {
        let source =
            std::fs::read_to_string(demo_file(desk)).unwrap_or_else(|err| panic!("{desk}: {err}"));
        let sends: Vec<&str> = source
            .lines()
            .filter(|line| line.starts_with("@\"assay\"!("))
            .collect();
        assert_eq!(
            sends,
            vec![
                format!("@\"assay\"!(lambda:Term`{NF_IDENTITY}`) |"),
                format!("@\"assay\"!(lambda:Term`{NF_MIRROR}`) |"),
                format!("@\"assay\"!(lambda:Term`{NF_CONSTANT}`) |"),
            ],
            "{desk} must offer the desk exactly the three contract results, in this order"
        );
    }
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// Beat 3 — the guard selects the constant combinator out of three resting results
// ════════════════════════════════════════════════════════════════════════════════════════════

/// Beat 3's hook: the last seven lines of the desk file are the whole program — three sends and
/// the one guarded receive. The sheet prints them with `tail -7`.
#[test]
fn beat_3_the_desk_program_is_the_last_seven_lines_of_the_file() {
    let source = std::fs::read_to_string(demo_file("desk-accepts-constant.rho"))
        .expect("the demo ships desk-accepts-constant.rho");
    let tail: Vec<&str> = source.lines().rev().take(7).collect::<Vec<_>>();
    let tail: Vec<&str> = tail.into_iter().rev().collect();
    assert_eq!(
        tail,
        vec![
            "@\"assay\"!(lambda:Term`lam x. x`) |",
            "@\"assay\"!(lambda:Term`lam a. lam b. b`) |",
            "@\"assay\"!(lambda:Term`lam a. lam b. a`) |",
            "",
            "for(@lambda:Term`${r}` <- @\"assay\" where lambda:Term`${r}` == lambda:Term`lam a. lam b. a`) {",
            "  @\"OUT\"!(lambda:Term`${r}`)",
            "}",
        ],
        "`tail -7` must print exactly the program the audience is told it is reading"
    );
}

/// Beat 3, what the audience sees: the accepted result, and NOTHING else.
///
/// **Exactly one datum, deliberately.** An earlier draft also published a human-readable label,
/// and two data resting on one channel come back in a scheduler-chosen order — nine sequential
/// hand-runs put the term first and the first run under parallel load swapped them, caught by
/// [`every_demo_file_is_byte_identical_over_consecutive_runs`]. One observation per channel
/// cannot be misordered, so the run sheet's transcript is the transcript every time.
#[test]
fn beat_3_the_desk_publishes_only_the_constant_combinator() {
    let stdout = transcript("desk-accepts-constant.rho");
    assert_eq!(
        out_observations(&stdout),
        vec!["⟦λ.λ.1⟧"],
        "exactly one result settles, and it is the constant combinator"
    );
    assert!(
        stdout.contains("mode: process → running to rest on the f1r3node reducer"),
        "the desk is a PROCESS, so it runs to rest\nstdout:\n{stdout}"
    );
}

/// Beat 3, the half the interpreter cannot show: the two REFUSED results are still on `@"assay"`,
/// read from the same quiescent store as the settled one. Nothing the guard refused was consumed,
/// and nothing was fabricated.
#[tokio::test(flavor = "multi_thread")]
async fn beat_3_the_two_refused_results_are_still_resting_on_the_book() {
    let identity = resting_display_of(NF_IDENTITY).await;
    let mirror = resting_display_of(NF_MIRROR).await;
    let constant = resting_display_of(NF_CONSTANT).await;
    let mut refused = vec![identity, mirror];
    refused.sort();

    let observed = rest_on_channels_of_demo("desk-accepts-constant.rho", &["assay"]).await;
    assert_eq!(
        observed,
        vec![("assay".to_string(), refused.clone())],
        "the identity and the mirror combinator are left behind, untouched, on @\"assay\""
    );
    assert!(
        !refused.contains(&constant),
        "the accepted result must NOT also be resting — it was consumed by the COMM that settled it"
    );
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// Beat 4 — one changed token; the SAME resting set yields a DIFFERENT result
// ════════════════════════════════════════════════════════════════════════════════════════════

/// Beat 4, what the audience sees. This is the beat that makes the filter's role unarguable: the
/// data, the channel and the receive pattern are identical to Beat 3's and only the term on the
/// right of the `==` differs, so the guard — and nothing else — chose.
#[test]
fn beat_4_the_same_set_under_a_different_predicate_settles_the_identity() {
    let stdout = transcript("desk-accepts-identity.rho");
    assert_eq!(
        out_observations(&stdout),
        vec!["⟦λ.0⟧"],
        "the identity settles out of the very same three results Beat 3 filtered"
    );
}

/// Beat 4's resting half — and the proof that Beat 3 left the identity behind rather than
/// destroying it: here the identity settles, and it is Beat 3's ACCEPTED result (the constant
/// combinator) that is now among those left on the book.
#[tokio::test(flavor = "multi_thread")]
async fn beat_4_the_constant_combinator_is_among_what_this_desk_leaves_behind() {
    let mirror = resting_display_of(NF_MIRROR).await;
    let constant = resting_display_of(NF_CONSTANT).await;
    let mut refused = vec![mirror, constant.clone()];
    refused.sort();

    let observed = rest_on_channels_of_demo("desk-accepts-identity.rho", &["assay"]).await;
    assert_eq!(
        observed,
        vec![("assay".to_string(), refused)],
        "the mirror and the CONSTANT combinator rest here — the constant is the one Beat 3 settled, \
         so neither desk consumed what its guard refused"
    );
}

/// The two desks differ in exactly one token — the term on the right of the `==`. Anything else
/// differing would mean Beat 4 is not the controlled experiment it is presented as.
#[test]
fn the_two_desks_differ_only_in_the_guards_comparison_term() {
    let constant_desk = std::fs::read_to_string(demo_file("desk-accepts-constant.rho"))
        .expect("the demo ships desk-accepts-constant.rho");
    let identity_desk = std::fs::read_to_string(demo_file("desk-accepts-identity.rho"))
        .expect("the demo ships desk-accepts-identity.rho");
    let program_of = |source: &str| -> Vec<String> {
        source
            .lines()
            .filter(|line| !line.trim_start().starts_with("//") && !line.trim().is_empty())
            .map(str::to_string)
            .collect()
    };
    let constant_program = program_of(&constant_desk);
    let identity_program = program_of(&identity_desk);
    assert_eq!(
        constant_program.len(),
        identity_program.len(),
        "the two desks must be the same program shape"
    );
    let differing: Vec<(&String, &String)> = constant_program
        .iter()
        .zip(identity_program.iter())
        .filter(|(left, right)| left != right)
        .collect();
    assert_eq!(
        differing.len(),
        1,
        "exactly ONE line may differ — the guarded receive, and within it only the comparison \
         term (left = constant desk, right = identity desk): {differing:?}"
    );
    assert!(
        differing[0]
            .0
            .contains("where lambda:Term`${r}` == lambda:Term`lam a. lam b. a`")
            && differing[0]
                .1
                .contains("where lambda:Term`${r}` == lambda:Term`lam x. x`"),
        "the load-bearing difference is the guard's comparison term: {:?}",
        differing[0]
    );
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// Beat 5a — the reduction is load-bearing: the un-reduced arrival is refused
// ════════════════════════════════════════════════════════════════════════════════════════════

/// Beat 5a. Beat 3's guard, verbatim, over Contract C **as it arrives** — the application
/// `(I K)` rather than its normal form. The desk refuses it, which is what makes Beats 1–2
/// load-bearing rather than decorative: the reduction is the step that turns an unacceptable
/// arrival into an acceptable result.
///
/// It also refutes a whole class of wrong-reason passes: a guard comparing SOURCE TEXT, or
/// matching loosely on the guest-term envelope rather than on the term, would accept this datum.
#[test]
fn beat_5a_the_unreduced_arrival_is_refused() {
    let stdout = transcript("desk-refuses-the-unreduced-arrival.rho");
    assert_eq!(
        out_observations(&stdout),
        Vec::<String>::new(),
        "(I K) is not K until something reduces it, so the desk must refuse it"
    );
    assert!(
        stdout.contains("@\"OUT\": (the program rested without publishing any observation)"),
        "the accept continuation must not have fired\nstdout:\n{stdout}"
    );
}

/// Beat 5a is a CONTROLLED experiment only if the guard is Beat 3's, unchanged. Asserted on the
/// committed source: the two files' guarded-receive lines must be character-identical, and the
/// only datum offered here must be the un-reduced arrival.
#[test]
fn beat_5a_changes_the_datum_and_nothing_else() {
    let guard_line_of = |demo: &str| -> String {
        let source = std::fs::read_to_string(demo_file(demo))
            .unwrap_or_else(|err| panic!("the demo ships {demo}: {err}"));
        source
            .lines()
            .find(|line| line.starts_with("for(@lam"))
            .unwrap_or_else(|| panic!("{demo} has a guarded receive"))
            .to_string()
    };
    assert_eq!(
        guard_line_of("desk-refuses-the-unreduced-arrival.rho"),
        guard_line_of("desk-accepts-constant.rho"),
        "Beat 5a must ask the SAME question Beat 3 asked — only the datum may differ"
    );

    let source = std::fs::read_to_string(demo_file("desk-refuses-the-unreduced-arrival.rho"))
        .expect("the demo ships desk-refuses-the-unreduced-arrival.rho");
    let sends: Vec<&str> = source
        .lines()
        .filter(|line| line.starts_with("@\"assay\"!("))
        .collect();
    assert_eq!(
        sends,
        vec![format!("@\"assay\"!(lambda:Term`{UNREDUCED_ARRIVAL}`) |")],
        "exactly one datum is offered, and it is Contract C as it arrives"
    );
}

/// The arrival really does reduce to the constant combinator — otherwise "the desk refused it
/// because it had not been reduced" would be a story about a term that never becomes acceptable
/// at all. Driven as a bare term through the same interpreter, it fires once and lands on K.
#[test]
fn beat_5a_the_refused_arrival_is_exactly_what_contract_c_reduces() {
    let source = std::fs::read_to_string(demo_file("contract-c.rho"))
        .expect("the demo ships contract-c.rho");
    assert_eq!(
        source.lines().last().expect("contract-c.rho is non-empty"),
        format!("lambda:Term`{UNREDUCED_ARRIVAL}`"),
        "the datum Beat 5a offers IS contract-c.rho's term, verbatim"
    );
    assert_eq!(
        out_observations(&transcript("contract-c.rho")),
        vec!["⟦λ.λ.1⟧"],
        "…and that term reduces to the very constant combinator the guard asks for"
    );
}

/// Beat 5a's resting half: the refused arrival is not consumed either.
#[tokio::test(flavor = "multi_thread")]
async fn beat_5a_the_unreduced_arrival_is_refused_and_left_resting() {
    let arrival = resting_display_of(UNREDUCED_ARRIVAL).await;
    let observed =
        rest_on_channels_of_demo("desk-refuses-the-unreduced-arrival.rho", &["OUT", "assay"]).await;
    assert_eq!(
        observed,
        vec![("OUT".to_string(), Vec::<String>::new()), ("assay".to_string(), vec![arrival]),],
        "nothing settled, and the un-reduced arrival is still on the book"
    );
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// Beat 5b — the negative control: a predicate no result satisfies
// ════════════════════════════════════════════════════════════════════════════════════════════

/// Beat 5. The search exhausts and the desk publishes nothing. Without this, "exactly one
/// settled" is compatible with a guard that simply admits whatever it is handed first.
#[test]
fn beat_5_a_predicate_no_result_satisfies_settles_nothing() {
    let stdout = transcript("desk-accepts-nothing.rho");
    assert_eq!(
        out_observations(&stdout),
        Vec::<String>::new(),
        "no result satisfies the predicate, so nothing may be published"
    );
    assert!(
        stdout.contains("@\"OUT\": (the program rested without publishing any observation)"),
        "the interpreter must report an empty OUT explicitly\nstdout:\n{stdout}"
    );
}

/// Beat 5's resting half: ALL THREE results are still on the book. This is the upper bound that
/// makes the other two desks' resting sets meaningful — the channel starts with three and the
/// guard is what removes one.
#[tokio::test(flavor = "multi_thread")]
async fn beat_5_a_refusing_guard_consumes_nothing_at_all() {
    let all = all_three_results().await;
    let observed = rest_on_channels_of_demo("desk-accepts-nothing.rho", &["assay"]).await;
    assert_eq!(
        observed,
        vec![("assay".to_string(), all)],
        "a guard that refuses every candidate must leave every candidate resting"
    );
}

/// The refusal is a DECISION, not an error: the same program shape with a satisfiable predicate
/// settles. Asserted here as one statement so "nothing settled" can never be read as "the guard
/// could not be evaluated".
#[tokio::test(flavor = "multi_thread")]
async fn the_refusal_is_a_decision_because_the_same_shape_settles_under_two_other_predicates() {
    let constant = resting_display_of(NF_CONSTANT).await;
    let identity = resting_display_of(NF_IDENTITY).await;

    let settled_constant = rest_on_channels_of_demo("desk-accepts-constant.rho", &["OUT"]).await;
    assert!(
        settled_constant[0].1.contains(&constant),
        "the constant desk settles the constant combinator: {settled_constant:?}"
    );
    let settled_identity = rest_on_channels_of_demo("desk-accepts-identity.rho", &["OUT"]).await;
    assert!(
        settled_identity[0].1.contains(&identity),
        "the identity desk settles the identity combinator: {settled_identity:?}"
    );
    let settled_nothing = rest_on_channels_of_demo("desk-accepts-nothing.rho", &["OUT"]).await;
    assert_eq!(
        settled_nothing,
        vec![("OUT".to_string(), Vec::<String>::new())],
        "and the unsatisfiable predicate settles nothing — three outcomes no single defect spans"
    );
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// Determinism — the presenter's transcript is reproducible, not a lucky schedule
// ════════════════════════════════════════════════════════════════════════════════════════════

/// Every demo file produces BYTE-IDENTICAL stdout over consecutive runs. A demo that flakes in
/// front of an audience is worse than a smaller one that does not, so this is a gate, not a note.
#[test]
fn every_demo_file_is_byte_identical_over_consecutive_runs() {
    for demo in [
        "contract-a.rho",
        "contract-b.rho",
        "contract-c.rho",
        "desk-accepts-constant.rho",
        "desk-accepts-identity.rho",
        "desk-refuses-the-unreduced-arrival.rho",
        "desk-accepts-nothing.rho",
    ] {
        let first = transcript(demo);
        for run in 2..=3 {
            assert_eq!(
                transcript(demo),
                first,
                "{demo} differed between run 1 and run {run} — the run sheet's transcript would \
                 be a lucky schedule rather than the program's meaning"
            );
        }
    }
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// Script integrity — the sheet cannot drift from this test
// ════════════════════════════════════════════════════════════════════════════════════════════

/// Every fenced block of `RUN-SHEET.md`, in order, as its lines.
fn run_sheet_blocks() -> Vec<Vec<String>> {
    let sheet =
        std::fs::read_to_string(demo_file("RUN-SHEET.md")).expect("the demo ships a RUN-SHEET.md");
    let mut blocks = Vec::new();
    let mut current: Option<Vec<String>> = None;
    for line in sheet.lines() {
        if line.trim_start().starts_with("```") {
            match current.take() {
                Some(block) => blocks.push(block),
                None => current = Some(Vec::new()),
            }
            continue;
        }
        if let Some(block) = current.as_mut() {
            block.push(line.to_string());
        }
    }
    assert!(current.is_none(), "RUN-SHEET.md has an unbalanced code fence");
    blocks
}

/// The `$ command` lines of a fenced block (empty if the block is an output transcript).
fn commands_of(block: &[String]) -> Vec<String> {
    block
        .iter()
        .filter_map(|line| line.trim().strip_prefix("$ "))
        .filter(|command| !command.trim().is_empty())
        .map(|command| command.trim().to_string())
        .collect()
}

/// Every `$ command` line printed in a fenced block of `RUN-SHEET.md`.
fn run_sheet_commands() -> Vec<String> {
    run_sheet_blocks()
        .iter()
        .flat_map(|block| commands_of(block))
        .collect()
}

/// Every `(command, expected output)` pair the sheet shows: a fence holding exactly one command,
/// immediately followed by a fence holding no command at all. The setup build line is therefore
/// unpaired (the next fence is Beat 1's command), which is correct — this test cannot run cargo.
fn run_sheet_command_transcripts() -> Vec<(String, String)> {
    let blocks = run_sheet_blocks();
    let mut pairs = Vec::new();
    for (index, block) in blocks.iter().enumerate() {
        let commands = commands_of(block);
        let [command] = commands.as_slice() else {
            continue;
        };
        let Some(next) = blocks.get(index + 1) else {
            continue;
        };
        if !commands_of(next).is_empty() {
            continue;
        }
        pairs.push((command.clone(), next.join("\n")));
    }
    pairs
}

/// The run sheet's command lines and the lines this file drives are the SAME set. A beat added to
/// the sheet without coverage, or a beat whose spelling drifts, fails here — which is what makes
/// the sheet an executed script rather than a narrative.
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

/// **The sheet is executable.** Every command the sheet shows with an expected transcript is run
/// here and its output compared VERBATIM against the block the sheet prints. This is the
/// strongest form of "every command on this page produces the stated output": a beat whose
/// output drifts by one character — a changed comment count, a renamed channel, a reordered
/// observation — fails here, so the presenter can never read a stale transcript aloud.
#[test]
fn every_transcript_in_the_run_sheet_is_the_observed_output() {
    let pairs = run_sheet_command_transcripts();
    assert_eq!(
        pairs.len(),
        9,
        "the sheet shows 9 commands with transcripts (7 interpreter runs, 2 source listings): \
         {:?}",
        pairs.iter().map(|(command, _)| command).collect::<Vec<_>>()
    );
    for (command, expected) in pairs {
        let observed = if let Some(path) = command.strip_prefix("target/debug/rholang ") {
            let demo = path
                .strip_prefix(&format!("{DEMO_DIR}/"))
                .unwrap_or_else(|| panic!("the sheet runs demo files from {DEMO_DIR}: {command}"));
            transcript(demo)
        } else if let Some(rest) = command.strip_prefix("tail -") {
            let (count, path) = rest
                .split_once(' ')
                .unwrap_or_else(|| panic!("a `tail -N PATH` line: {command}"));
            let count: usize = count
                .parse()
                .unwrap_or_else(|_| panic!("a numeric tail count: {command}"));
            let demo = path
                .strip_prefix(&format!("{DEMO_DIR}/"))
                .unwrap_or_else(|| panic!("the sheet lists demo files from {DEMO_DIR}: {command}"));
            let source = std::fs::read_to_string(demo_file(demo))
                .unwrap_or_else(|err| panic!("the demo ships {demo}: {err}"));
            let lines: Vec<&str> = source.lines().collect();
            lines[lines.len().saturating_sub(count)..].join("\n")
        } else {
            panic!("the sheet pairs a transcript with an unrecognized command: {command}");
        };
        assert_eq!(
            observed.trim_end(),
            expected.trim_end(),
            "`$ {command}` did not produce the transcript RUN-SHEET.md prints"
        );
    }
}

/// The sheet's build line must name the bin target and the exact features it requires, so a
/// presenter who follows the sheet ends up with the binary this test gates.
#[test]
fn the_run_sheet_build_line_names_the_features_the_binary_requires() {
    assert!(
        BUILD_COMMAND.contains("--bin rholang")
            && BUILD_COMMAND.contains("rholang-runtime")
            && BUILD_COMMAND.contains("lambda-runtime"),
        "the sheet's build line must build the rholang bin with both required features"
    );
    assert!(
        run_sheet_commands().contains(&BUILD_COMMAND.to_string()),
        "the sheet must actually print the build line"
    );
}
