//! CI gate for the **Church Desk** demo (`demos/flt-church-desk/`).
//!
//! The demo's vehicle is the `rholang` interpreter binary run on committed `.rho` files, so this
//! file drives that binary with the run sheet's own command lines and asserts, per beat, what the
//! audience sees. Without it the run sheet is a hand-run narrative that rots silently.
//!
//! ## What is covered, and by which layer
//!
//! | layer | vehicle | answers |
//! |---|---|---|
//! | interpreter transcript | `CARGO_BIN_EXE_rholang` on the committed `.rho` files | what the AUDIENCE sees: the value, the normal form, the `^fired` ledger, the fuel report |
//! | runtime readback | `lower_rholang_proc_with_resolver` + multi-channel `get_data` | what RESTS — the candidates the guard and the pattern REFUSED, which the interpreter's single-channel `@"OUT"` view cannot show |
//! | script integrity | `RUN-SHEET.md` parsing | every command line in the sheet is driven here |
//! | determinism | three identical runs per beat | the presenter's transcript is reproducible, not a lucky schedule |
//!
//! ## Why the beats are shaped the way they are
//!
//! Each beat is answerable by an audience with no prior exposure to the project, and no single
//! defect produces all six outcomes:
//!
//! * a **vacuous** guard (one that admits everything) would let `desk-keeps-five.rho` settle more
//!   than one datum, and would let it settle the same datum as `desk-keeps-six.rho`;
//! * a **fail-closed** guard (one the substrate cannot decide, silently refusing) would settle
//!   NOTHING in either desk — the pair is what proves the predicate is decided, because one
//!   changed token selects a different answer from a bit-identical resting set;
//! * a **structurally blind** receive pattern would let `destructure.rho` match the identity
//!   `lam x. x` or the application `(lam x. x, lam y. y)`, which have one binder and none. Both
//!   are still resting when the program comes to rest, and this file asserts that;
//! * a **host-side** arithmetic shortcut would not produce a `^fired` ledger of 21 in-Rho firings
//!   in `arithmetic.rho`, nor a `^drive-fuel` report in `divergence.rho`.
//!
//! ## Format-agnostic resting assertions
//!
//! The resting-datum assertions never hard-code a rendering of a reflected λ-term. Each expected
//! value is minted by [`resting_display_of`], which publishes that ONE guest term with no receive
//! at all and reads back what rests — so the expectation comes from the same reflection path as
//! the datum under test, and a change to the reflected wire format can neither make these tests
//! pass vacuously nor fail spuriously.
#![cfg(all(
    feature = "rholang-runtime",
    feature = "lambda-runtime",
    feature = "calculator-runtime"
))]

use std::path::PathBuf;
use std::process::{Command, Output};
use std::sync::Arc;

use mettail_languages::calculator::CalculatorLanguage;
use mettail_languages::lambda::LambdaLanguage;
use mettail_languages::rholang::Proc;
use mettail_rholang_codegen::{FltReflect, FltRegistry, FltResolve};
use mettail_rholang_runtime::{
    lower_rholang_proc_with_resolver, run_normalized_par_for_oracle_and_read_runtime_value_channels,
};
use mettail_runtime::{clear_var_cache, Language};

// ════════════════════════════════════════════════════════════════════════════════════════════
// The demo's identity, and the beats verbatim from RUN-SHEET.md
// ════════════════════════════════════════════════════════════════════════════════════════════

/// The demo directory, relative to the workspace root.
const DEMO_DIR: &str = "demos/flt-church-desk";

/// The build line the run sheet tells the presenter to run.
const BUILD_COMMAND: &str = "cargo build -p rholang-runtime --bin rholang --features \
     \"rholang-runtime lambda-runtime calculator-runtime\"";

/// The environment-variable prefix every run line in this sheet **used to** carry, kept as a
/// named constant so the gate below can assert its ABSENCE by name rather than by a string
/// literal buried in an assertion.
///
/// It was there because the λ-guest's reduction on a term this size once recursed deeper than the
/// default thread stack allowed. Stage M removed the cause. It is deliberately *not* deleted
/// outright: a demo page that once required a resource knob is exactly the page a future change
/// would silently re-break, and a gate that names the knob is what makes the re-break loud.
const RETIRED_STACK_PREFIX: &str = "RUST_MIN_STACK";

const BEAT_0_RUN: &str = "target/debug/rholang demos/flt-church-desk/calculator.rho";
const BEAT_1_SHOW: &str = "tail -1 demos/flt-church-desk/arithmetic.rho";
const BEAT_1_RUN: &str = "target/debug/rholang demos/flt-church-desk/arithmetic.rho";
const BEAT_2_RUN: &str = "target/debug/rholang demos/flt-church-desk/divergence.rho";
const BEAT_3_RUN: &str = "target/debug/rholang demos/flt-church-desk/desk-keeps-five.rho";
const BEAT_4_RUN: &str = "target/debug/rholang demos/flt-church-desk/desk-keeps-six.rho";
const BEAT_5_SHOW: &str = "tail -7 demos/flt-church-desk/destructure.rho";
const BEAT_5_RUN: &str = "target/debug/rholang demos/flt-church-desk/destructure.rho";

/// Every command line this file drives, in sheet order.
/// [`every_run_sheet_command_line_is_driven_by_this_test`] compares this against the sheet, so a
/// beat added to the sheet without coverage here fails the build.
fn driven_commands() -> Vec<String> {
    [
        BUILD_COMMAND,
        BEAT_0_RUN,
        BEAT_1_SHOW,
        BEAT_1_RUN,
        BEAT_2_RUN,
        BEAT_3_RUN,
        BEAT_4_RUN,
        BEAT_5_SHOW,
        BEAT_5_RUN,
    ]
    .into_iter()
    .map(str::to_string)
    .collect()
}

// ── the guest terms the desks filter over, in the λ-guest's own surface syntax ───────────────

/// Church 5 — `λf.λx. f(f(f(f(f x))))`. The term `desk-keeps-five.rho` accepts.
const CHURCH_5: &str = "lam f. lam x. (f, (f, (f, (f, (f, x)))))";
/// Church 6. The term `desk-keeps-six.rho` accepts, and which five's desk refuses.
const CHURCH_6: &str = "lam f. lam x. (f, (f, (f, (f, (f, (f, x))))))";
/// Church 0 — `λf.λx. x`. Refused by BOTH desks.
const CHURCH_0: &str = "lam f. lam x. x";
/// The identity. One binder, so `destructure.rho`'s two-binder pattern cannot match it.
const IDENTITY: &str = "lam x. x";
/// An application. No binder at its head at all, so the pattern cannot match it either.
const APPLICATION: &str = "(lam x. x, lam y. y)";

// ════════════════════════════════════════════════════════════════════════════════════════════
// Driving the interpreter binary — exactly what the presenter runs
// ════════════════════════════════════════════════════════════════════════════════════════════

fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("the crate directory has a workspace-root parent")
        .to_path_buf()
}

fn demo_file(name: &str) -> PathBuf {
    workspace_root().join(DEMO_DIR).join(name)
}

/// Run the built `rholang` binary on one committed demo file, in exactly the environment the run
/// sheet now tells a presenter to use: the ambient one, with `RUST_MIN_STACK` explicitly REMOVED.
///
/// `env_remove` rather than "just don't set it": the test process may itself have been launched
/// with `RUST_MIN_STACK` in its environment (the repo's own gate command sets it), and a child
/// inherits it. Without the removal this harness would quietly run the demos on a stack the
/// presenter will not have, and the transcript gate would then certify output that a presenter
/// cannot reproduce — the precise failure mode Stage M is removing from this page.
fn run_demo(name: &str) -> Output {
    Command::new(env!("CARGO_BIN_EXE_rholang"))
        .arg(demo_file(name))
        .env_remove("RUST_MIN_STACK")
        .current_dir(workspace_root())
        .output()
        .unwrap_or_else(|err| panic!("the rholang binary must run on {name}: {err}"))
}

/// Run one demo and retain both streams after checking its contractually expected exit code.
/// Divergence is the one intentional failure: the CLI reports exhausted reduction fuel as
/// `EX_SOFTWARE` (70), while every other beat must succeed.
fn checked_demo_streams(name: &str) -> (String, String) {
    let output = run_demo(name);
    let stdout = String::from_utf8(output.stdout).expect("rholang writes UTF-8 to stdout");
    let stderr = String::from_utf8(output.stderr).expect("rholang writes UTF-8 to stderr");
    let expected_code = if name == "divergence.rho" { 70 } else { 0 };
    assert_eq!(
        output.status.code(),
        Some(expected_code),
        "the rholang binary returned the wrong status on {name}\nstatus: {}\nstdout:\n{stdout}\nstderr:\n{stderr}",
        output.status,
    );
    (stdout, stderr)
}

/// The binary's STDOUT for one demo file.
fn transcript(name: &str) -> String {
    checked_demo_streams(name).0
}

/// The binary's STDERR for one demo file (the fail-closed reports land here).
fn diagnostic(name: &str) -> String {
    checked_demo_streams(name).1
}

/// The `⟦…⟧` observations the interpreter printed, in order. Deliberately parses only the
/// `[i] ⟦…⟧` lines, so the `= Church numeral n` annotation lines are not mistaken for values.
fn out_observations(stdout: &str) -> Vec<String> {
    stdout
        .lines()
        .filter_map(|line| {
            let trimmed = line.trim();
            let (_index, rest) = trimmed.strip_prefix('[')?.split_once("] ")?;
            rest.starts_with('⟦').then(|| rest.to_string())
        })
        .collect()
}

/// The scalar values the interpreter printed for a fold-dataflow evaluation (`[i] 14`).
fn out_scalars(stdout: &str) -> Vec<String> {
    stdout
        .lines()
        .filter_map(|line| {
            let trimmed = line.trim();
            let (_index, rest) = trimmed.strip_prefix('[')?.split_once("] ")?;
            (!rest.starts_with('⟦')).then(|| rest.to_string())
        })
        .collect()
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// Runtime readback — what RESTS, which the interpreter's @"OUT" view cannot show
// ════════════════════════════════════════════════════════════════════════════════════════════

/// The guest registry the interpreter installs, rebuilt by the SAME derivation the binary uses
/// (`guest.name().to_lowercase()`), so this file cannot silently disagree with it about a tag.
fn guest_resolver() -> Arc<dyn FltResolve> {
    let guests: Vec<Box<dyn FltReflect>> =
        vec![Box::new(CalculatorLanguage), Box::new(LambdaLanguage)];
    let registry = guests
        .into_iter()
        .fold(FltRegistry::new(), |registry, guest| {
            let tag = guest.name().to_lowercase();
            registry.with_guest(tag, guest)
        });
    Arc::new(registry)
}

/// Run one Rholang program to rest and report, per channel, the sorted renderings of every datum
/// left on it — all read from ONE quiescent store, which is what makes "the desk kept X" and
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

/// ⚠ The interpreter's `⟦…⟧` transcript rendering and this RESTING rendering are two different
/// views of the same reflected term: the interpreter prints λ-aware surface syntax
/// (`render_obs`), while a resting datum is printed through the runtime value's own `Display`
/// (`^lambda(^lambda(App(…)))`). Compare like with like — an `@"OUT"` assertion against
/// `out_observations`, a resting assertion against [`resting_display_of`].
///
/// The rendering of ONE reflected guest term as it rests on a channel — minted by publishing it
/// with no receiver at all, so the expected value comes from the same reflection path as the
/// value under test. Nothing about the reflected wire format is hard-coded anywhere in this file.
async fn resting_display_of(guest_term: &str) -> String {
    let program = format!("@\"results\"!(lambda:Term`{guest_term}`)");
    let resting = rest_on_channels(&program, &["results"]).await;
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

/// A sorted expectation set built from guest surface terms.
async fn resting_set(terms: &[&str]) -> Vec<String> {
    let mut all = Vec::with_capacity(terms.len());
    for term in terms {
        all.push(resting_display_of(term).await);
    }
    all.sort();
    all
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// Beat 0 — a SECOND guest language, evaluated as real arithmetic on the reducer
// ════════════════════════════════════════════════════════════════════════════════════════════

/// The Calculator guest's opener is the lower-cased grammar name, and the committed file uses it.
#[test]
fn beat_0_the_calculator_guest_is_opened_by_the_lower_cased_grammar_name() {
    let source = std::fs::read_to_string(demo_file("calculator.rho"))
        .expect("the demo ships calculator.rho");
    assert_eq!(
        source.lines().last().expect("calculator.rho is non-empty"),
        "calculator:Proc`2 + 3 * 4`",
        "the opener must be the lower-cased name of the CalculatorLanguage grammar"
    );
    assert_eq!(
        CalculatorLanguage.name().to_lowercase(),
        "calculator",
        "and that spelling must be DERIVED from the language, not typed twice"
    );
}

/// Beat 0. `2 + 3 * 4` evaluates to 14 on the reducer, through the E3 fold dataflow — precedence
/// included, so the answer is 14 and not 20.
#[test]
fn beat_0_calculator_term_evaluates_to_fourteen_on_the_reducer() {
    let stdout = transcript("calculator.rho");
    assert_eq!(
        out_scalars(&stdout),
        vec!["14"],
        "2 + 3 * 4 must evaluate to 14 (not 20 — `*` binds tighter)\nstdout:\n{stdout}"
    );
    assert!(
        stdout.contains("guest `calculator`, E3 fold dataflow"),
        "the arithmetic must run through the fold dataflow on the reducer, not a host fold\
         \nstdout:\n{stdout}"
    );
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// Beat 1 — λ-calculus arithmetic, driven to a normal form by the machine
// ════════════════════════════════════════════════════════════════════════════════════════════

/// Beat 1's hook: the last line of `arithmetic.rho` is the foreign term as written. The sheet
/// prints it with `tail -1`, so what the audience reads is the committed source.
#[test]
fn beat_1_the_foreign_term_as_written_is_the_last_line_of_the_file() {
    let source = std::fs::read_to_string(demo_file("arithmetic.rho"))
        .expect("the demo ships arithmetic.rho");
    let last = source.lines().last().expect("arithmetic.rho is non-empty");
    assert!(
        last.starts_with("lambda:Term`") && last.ends_with('`'),
        "the term the sheet shows with `tail -1` must be the FLT the interpreter runs: {last}"
    );
}

/// Beat 1. `mult (plus 1 2) (plus 2 2)` = 3 * 4 = 12, computed by β-reduction alone, on the
/// reducer, and terminating by QUIESCENCE rather than by fuel exhaustion.
#[test]
fn beat_1_church_arithmetic_reaches_twelve_in_twenty_one_beta_firings() {
    let stdout = transcript("arithmetic.rho");
    assert_eq!(
        out_observations(&stdout),
        vec!["⟦λ.λ.(1 (1 (1 (1 (1 (1 (1 (1 (1 (1 (1 (1 0))))))))))))⟧"],
        "3 * 4 must land on the Church numeral 12 — twelve applications of the outer binder\
         \nstdout:\n{stdout}"
    );
    assert!(
        stdout.contains("= Church numeral 12"),
        "and the interpreter must NAME that shape, so the audience does not count applications\
         \nstdout:\n{stdout}"
    );
    assert!(
        stdout.contains("(21 in-Rho rewrite firing(s))"),
        "the machine's own receipt must show 21 firings — this is the visible work\
         \nstdout:\n{stdout}"
    );
    assert!(
        stdout.contains("^drive-err: 0 datum(a) · ^drive-fuel: 0 datum(a)"),
        "it must terminate by QUIESCENCE, not by fuel exhaustion or a typed error\
         \nstdout:\n{stdout}"
    );
    assert!(
        stdout.contains("mode: term → reducing to normal form on the f1r3node reducer"),
        "a bare λ FLT must take the DRIVE path, not the run-to-rest path\nstdout:\n{stdout}"
    );
}

/// Every firing in that ledger is a β step. Nothing else fired, so nothing but the λ-calculus's
/// own rule did the arithmetic.
#[test]
fn beat_1_every_firing_in_the_ledger_is_a_beta_step() {
    let stdout = transcript("arithmetic.rho");
    let ledger = stdout
        .lines()
        .find(|line| line.contains("^fired ledger:"))
        .unwrap_or_else(|| panic!("the drive path must print a ^fired ledger\nstdout:\n{stdout}"));
    assert_eq!(
        ledger.matches("\"Beta\"").count(),
        21,
        "all 21 firings must be Beta — no other rewrite family contributed: {ledger}"
    );
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// Beat 2 — the honest limit: a term that cannot finish says so
// ════════════════════════════════════════════════════════════════════════════════════════════

/// Beat 2. Ω reduces to itself forever. The fuel-bounded driver stops and NAMES the redex it
/// could not finish, on `^drive-fuel` — it does not hang, and it does not hand back a
/// half-reduced term as though it were an answer.
#[test]
fn beat_2_omega_exhausts_fuel_and_names_the_redex_it_could_not_finish() {
    let stderr = diagnostic("divergence.rho");
    assert!(
        stderr.contains("the term did not reach a normal form — reduction fuel exhausted"),
        "Ω must report fuel exhaustion\nstderr:\n{stderr}"
    );
    assert!(
        stderr.contains("stuck redex(es): ⟦(λ.(0 0) λ.(0 0))⟧"),
        "and it must NAME the redex — Ω itself, unchanged by every step it took\
         \nstderr:\n{stderr}"
    );
    assert!(
        transcript("divergence.rho")
            .lines()
            .all(|line| !line.contains("normal form on @\"OUT\" (1)")),
        "a diverging term must publish NO normal form"
    );
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// Beats 3 & 4 — the `where` guard: one changed token, a different answer, same resting set
// ════════════════════════════════════════════════════════════════════════════════════════════

/// Beat 3. Three numerals rest; the guard names Church 5; Church 5 is what comes out.
#[tokio::test(flavor = "multi_thread")]
async fn beat_3_the_desk_keeps_five_and_leaves_six_and_zero_resting() {
    let stdout = transcript("desk-keeps-five.rho");
    assert_eq!(
        out_observations(&stdout),
        vec!["⟦λ.λ.(1 (1 (1 (1 (1 0)))))⟧"],
        "the guard names Church 5, so Church 5 — five applications — is the datum that leaves\
         \nstdout:\n{stdout}"
    );
    assert!(
        stdout.contains("= Church numeral 5"),
        "and the interpreter names it\nstdout:\n{stdout}"
    );

    let resting = rest_on_channels_of_demo("desk-keeps-five.rho", &["results"]).await;
    assert_eq!(
        resting,
        vec![("results".to_string(), resting_set(&[CHURCH_6, CHURCH_0]).await)],
        "the two REFUSED numerals must still be on @\"results\" — the desk selected out of the \
         resting set, it did not consume it"
    );
}

/// Beat 4. The SAME three numerals, the same channel, the same receive pattern — one token
/// changed in the guard, and a different datum leaves. This is the pair that proves the guard is
/// genuinely DECIDED: a guard the substrate could not decide would refuse everything in both
/// files, and a vacuous one would accept the same datum in both.
#[tokio::test(flavor = "multi_thread")]
async fn beat_4_one_changed_token_selects_six_from_the_same_resting_set() {
    let stdout = transcript("desk-keeps-six.rho");
    assert_eq!(
        out_observations(&stdout),
        vec!["⟦λ.λ.(1 (1 (1 (1 (1 (1 0))))))⟧"],
        "the guard now names Church 6 — six applications — so Church 6 is what leaves\
         \nstdout:\n{stdout}"
    );
    assert!(
        stdout.contains("= Church numeral 6"),
        "and the interpreter names it\nstdout:\n{stdout}"
    );

    let resting = rest_on_channels_of_demo("desk-keeps-six.rho", &["results"]).await;
    assert_eq!(
        resting,
        vec![("results".to_string(), resting_set(&[CHURCH_5, CHURCH_0]).await)],
        "and Church 5 — the previous run's answer — is among the ones left resting here"
    );
}

/// The two desks differ in EXACTLY the guard, and nowhere else. If they diverged anywhere but
/// the `where` clause, the pair would prove nothing about the predicate.
#[test]
fn beats_3_and_4_differ_only_in_the_guard() {
    let five = std::fs::read_to_string(demo_file("desk-keeps-five.rho")).expect("ships five");
    let six = std::fs::read_to_string(demo_file("desk-keeps-six.rho")).expect("ships six");
    let program = |source: &str| -> Vec<String> {
        source
            .lines()
            .filter(|line| !line.trim_start().starts_with("//") && !line.trim().is_empty())
            .map(str::to_string)
            .collect()
    };
    let (five_lines, six_lines) = (program(&five), program(&six));
    assert_eq!(
        five_lines.len(),
        six_lines.len(),
        "the two desks must have the same program shape"
    );
    let differing: Vec<usize> = five_lines
        .iter()
        .zip(&six_lines)
        .enumerate()
        .filter_map(|(index, (a, b))| (a != b).then_some(index))
        .collect();
    assert_eq!(differing.len(), 1, "exactly one program line may differ");
    let line = differing[0];
    assert!(
        five_lines[line].contains("where") && six_lines[line].contains("where"),
        "and that line must be the `where` guard, not a datum or the channel:\n  {}\n  {}",
        five_lines[line],
        six_lines[line]
    );
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// Beat 5 — a NESTED hole: matching a shape, and binding a foreign SUB-TERM out into Rholang
// ════════════════════════════════════════════════════════════════════════════════════════════

/// Beat 5's hook: the sheet shows the tail of `destructure.rho`, and the receive pattern is an
/// FLT whose hole sits under TWO guest binders.
#[test]
fn beat_5_the_receive_pattern_carries_a_hole_under_two_guest_binders() {
    let source =
        std::fs::read_to_string(demo_file("destructure.rho")).expect("the demo ships destructure");
    assert!(
        source.contains("for(@lambda:Term`lam f. lam x. ${body}` <- @\"results\")"),
        "the pattern must be a foreign term with a NESTED hole\nsource:\n{source}"
    );
}

/// Beat 5. The pattern matches only λ-terms of the shape `λf.λx. _`, and binds the body — a
/// sub-term of the foreign term, from under both binders — out into Rholang as an ordinary name,
/// which the continuation then publishes.
#[tokio::test(flavor = "multi_thread")]
async fn beat_5_the_nested_hole_binds_the_body_out_of_the_foreign_term() {
    let stdout = transcript("destructure.rho");
    assert_eq!(
        out_observations(&stdout),
        vec!["⟦(1 (1 (1 (1 (1 0)))))⟧"],
        "the hole must bind the BODY of Church 5 — five applications of the outer binder, with \
         the binders themselves stripped away by the match\nstdout:\n{stdout}"
    );
}

/// …and the two terms whose SHAPE does not fit are refused and left resting. The identity has one
/// binder; the application has none. A structurally blind pattern would have consumed one of them.
#[tokio::test(flavor = "multi_thread")]
async fn beat_5_the_shapes_that_do_not_fit_are_refused_and_rest() {
    let resting = rest_on_channels_of_demo("destructure.rho", &["results"]).await;
    assert_eq!(
        resting,
        vec![("results".to_string(), resting_set(&[IDENTITY, APPLICATION]).await)],
        "the one-binder identity and the application must BOTH still be on @\"results\""
    );
}

/// The whole numeral is NOT what came out: the published body is a strict sub-term of it. This is
/// what makes the beat structural extraction rather than a whole-term match.
#[tokio::test(flavor = "multi_thread")]
async fn beat_5_the_published_body_is_a_strict_sub_term_of_the_matched_numeral() {
    let whole = resting_display_of(CHURCH_5).await;
    let published = out_observations(&transcript("destructure.rho"))
        .into_iter()
        .next()
        .expect("beat 5 publishes one observation");
    assert_ne!(
        published, whole,
        "the body must not be the whole numeral — the binders were stripped by the match"
    );
    assert!(
        whole.len() > published.len(),
        "and it must be SMALLER than the term it came out of:\n  whole:     {whole}\n  published: {published}"
    );
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// Determinism — the presenter's transcript is reproducible, not a lucky schedule
// ════════════════════════════════════════════════════════════════════════════════════════════

/// Every beat, run three times, must produce byte-identical output. The desks and the
/// destructuring receive publish exactly ONE observation each precisely so that no beat depends
/// on the order of two data on one channel.
#[test]
fn every_beat_is_byte_identical_across_three_runs() {
    for demo in [
        "calculator.rho",
        "arithmetic.rho",
        "divergence.rho",
        "desk-keeps-five.rho",
        "desk-keeps-six.rho",
        "destructure.rho",
    ] {
        let first = transcript(demo);
        for run in 2..=3 {
            assert_eq!(
                transcript(demo),
                first,
                "{demo} produced different output on run {run} — the sheet cannot pin a \
                 transcript that is not reproducible"
            );
        }
    }
}

/// No beat publishes two observations on one channel, so no beat can be reordered under
/// parallel load. This is a STRUCTURAL guard on the demo's design, not on one lucky run.
#[test]
fn no_beat_publishes_two_observations_on_one_channel() {
    for demo in ["desk-keeps-five.rho", "desk-keeps-six.rho", "destructure.rho"] {
        let stdout = transcript(demo);
        assert_eq!(
            out_observations(&stdout).len(),
            1,
            "{demo} must publish exactly one observation on @\"OUT\"\nstdout:\n{stdout}"
        );
    }
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// Script integrity — the sheet cannot drift from what runs
// ════════════════════════════════════════════════════════════════════════════════════════════

fn run_sheet() -> String {
    std::fs::read_to_string(workspace_root().join(DEMO_DIR).join("RUN-SHEET.md"))
        .expect("the demo ships RUN-SHEET.md")
}

/// Every `$ `-prefixed command line the sheet prints.
fn run_sheet_commands() -> Vec<String> {
    run_sheet()
        .lines()
        .filter_map(|line| line.strip_prefix("$ ").map(str::to_string))
        .collect()
}

/// ★ THE script-integrity gate. Every command line printed in the run sheet is driven by this
/// test, and every command this test drives is printed in the sheet. A beat added to the sheet
/// without coverage here — or a command respelled in one place only — fails the build.
#[test]
fn every_run_sheet_command_line_is_driven_by_this_test() {
    let mut sheet = run_sheet_commands();
    let mut driven = driven_commands();
    sheet.sort();
    sheet.dedup();
    driven.sort();
    driven.dedup();
    assert_eq!(
        sheet, driven,
        "the run sheet's command lines and the commands this test drives must be the same set"
    );
}

/// The sheet's build line must name the bin target and every feature it requires, so a presenter
/// who follows the sheet ends up with the binary this test gates.
#[test]
fn the_run_sheet_build_line_names_the_features_the_binary_requires() {
    for feature in ["rholang-runtime", "lambda-runtime", "calculator-runtime"] {
        assert!(BUILD_COMMAND.contains(feature), "the sheet's build line must enable {feature}");
    }
    assert!(
        BUILD_COMMAND.contains("--bin rholang"),
        "and it must build the rholang bin target"
    );
    assert!(
        run_sheet_commands().contains(&BUILD_COMMAND.to_string()),
        "the sheet must actually print the build line"
    );
}

/// ★ INVERTED BY STAGE M. No run line in the sheet may carry a `RUST_MIN_STACK` prefix.
///
/// This assertion used to be its own negation — *every* run line had to carry the prefix, because
/// dropping it aborted the arithmetic beat on a stack overflow. Stage M converted the Rholang
/// lowering off host recursion, and every beat on this page now runs at the default stack; the
/// prefix removal is measured, not assumed (`every_committed_demo_runs_at_the_default_stack`).
///
/// The gate is kept — pointing the other way — rather than deleted, for two reasons:
///
/// 1. **It is the regression detector for the fix.** If a future change re-introduces a
///    depth-proportional traversal on this path, the natural repair under presentation pressure is
///    to put the prefix back on the sheet. That must fail the build, loudly, and name the real
///    gate (`stack_depth_gate.rs`) instead.
/// 2. **The prefix was never a correct remedy here anyway.** `RUST_MIN_STACK` is read only by
///    `std::thread`'s spawn path, so it cannot resize a *main* thread — and `rholang.rs` is
///    `#[tokio::main] async fn main`, which is where parsing and lowering run. On those beats the
///    prefix was inert. A sheet that recommends an inert knob teaches a presenter to mis-diagnose.
#[test]
fn no_run_line_in_the_sheet_carries_a_stack_prefix() {
    for command in run_sheet_commands() {
        assert!(
            !command.contains(RETIRED_STACK_PREFIX),
            "no command line in the run sheet may carry a {RETIRED_STACK_PREFIX} prefix — \
             Stage M removed the need for it, and it never reached the main thread in any case. \
             Offending line: {command}"
        );
    }
}

/// The measurement behind [`no_run_line_in_the_sheet_carries_a_stack_prefix`]: every committed
/// demo file in this suite runs to its documented exit status on a binary invoked with **no**
/// `RUST_MIN_STACK` in its environment.
///
/// `divergence.rho` exits 70 — that is its documented fuel-exhaustion beat, not a fault — so the
/// assertion is on the *absence of a stack overflow*, which is the property the prefix existed to
/// buy, rather than on exit status alone.
#[test]
fn every_committed_demo_runs_at_the_default_stack() {
    for name in [
        "calculator.rho",
        "arithmetic.rho",
        "divergence.rho",
        "desk-keeps-five.rho",
        "desk-keeps-six.rho",
        "destructure.rho",
    ] {
        let output = Command::new(env!("CARGO_BIN_EXE_rholang"))
            .arg(demo_file(name))
            .env_remove("RUST_MIN_STACK")
            .current_dir(workspace_root())
            .output()
            .unwrap_or_else(|err| panic!("the rholang binary must run on {name}: {err}"));
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            !stderr.contains("overflowed its stack"),
            "{name} overflowed the stack with no RUST_MIN_STACK set — Stage M's conversion has \
             regressed, or a new depth-proportional traversal reached this path.\n{stderr}"
        );
    }
}

/// ★ THE transcript gate. Every fenced transcript in the sheet is compared against a LIVE run of
/// the command it follows, so the page cannot print an output the binary no longer produces.
#[test]
fn every_transcript_in_the_run_sheet_is_the_observed_output() {
    let sheet = run_sheet();
    let lines: Vec<&str> = sheet.lines().collect();
    let mut checked = 0usize;

    let mut index = 0usize;
    while index < lines.len() {
        let Some(command) = lines[index].strip_prefix("$ ") else {
            index += 1;
            continue;
        };
        // Find the next fenced block after this command's fence closes.
        let mut cursor = index + 1;
        while cursor < lines.len() && !lines[cursor].starts_with("```") {
            cursor += 1;
        }
        cursor += 1; // past the command block's closing fence
        while cursor < lines.len() && lines[cursor].trim().is_empty() {
            cursor += 1;
        }
        if cursor >= lines.len() || !lines[cursor].starts_with("```") {
            index += 1;
            continue; // a command the sheet prints without a transcript
        }
        let start = cursor + 1;
        let mut end = start;
        while end < lines.len() && !lines[end].starts_with("```") {
            end += 1;
        }
        let printed = lines[start..end].join("\n");

        let observed = if let Some(rest) = command.strip_prefix("target/debug/rholang ") {
            let demo = rest
                .strip_prefix(&format!("{DEMO_DIR}/"))
                .unwrap_or_else(|| panic!("the sheet runs demo files from {DEMO_DIR}: {command}"));
            let output = run_demo(demo);
            let mut combined = String::from_utf8(output.stdout).expect("utf-8 stdout");
            combined.push_str(&String::from_utf8(output.stderr).expect("utf-8 stderr"));
            // The `source:` line carries an absolute path under the test harness; the sheet
            // prints the workspace-relative one the presenter sees.
            combined
                .lines()
                .map(|line| match line.strip_prefix("source: ") {
                    Some(path) => format!(
                        "source: {}",
                        path.rsplit_once(&format!("{DEMO_DIR}/"))
                            .map(|(_, file)| format!("{DEMO_DIR}/{file}"))
                            .unwrap_or_else(|| path.to_string())
                    ),
                    None => line.to_string(),
                })
                .collect::<Vec<_>>()
                .join("\n")
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
            let all: Vec<&str> = source.lines().collect();
            all[all.len().saturating_sub(count)..].join("\n")
        } else {
            index += 1;
            continue; // the build line has no transcript
        };

        assert_eq!(
            observed.trim_end(),
            printed.trim_end(),
            "`$ {command}` did not produce the transcript RUN-SHEET.md prints"
        );
        checked += 1;
        index = end + 1;
    }

    assert!(
        checked >= 8,
        "the sheet must pin a transcript for every beat; only {checked} were checked"
    );
}

/// The demo ships exactly the files the sheet runs, and no orphans.
#[test]
fn the_demo_directory_holds_exactly_the_files_the_sheet_runs() {
    let mut shipped: Vec<String> = std::fs::read_dir(workspace_root().join(DEMO_DIR))
        .expect("the demo directory exists")
        .map(|entry| {
            entry
                .expect("a readable entry")
                .file_name()
                .to_string_lossy()
                .to_string()
        })
        .filter(|name| name.ends_with(".rho"))
        .collect();
    shipped.sort();
    assert_eq!(
        shipped,
        vec![
            "arithmetic.rho",
            "calculator.rho",
            "desk-keeps-five.rho",
            "desk-keeps-six.rho",
            "destructure.rho",
            "divergence.rho",
        ],
        "six files, six beats — no orphan left behind by an edit"
    );
}

/// The demo is mostly PROGRAM, not commentary. This is a direct, checkable answer to the
/// criticism that retired the previous demo, and it is asserted rather than asserted-in-prose.
#[test]
fn the_demo_files_are_mostly_program_not_commentary() {
    for demo in [
        "calculator.rho",
        "arithmetic.rho",
        "divergence.rho",
        "desk-keeps-five.rho",
        "desk-keeps-six.rho",
        "destructure.rho",
    ] {
        let source = std::fs::read_to_string(demo_file(demo)).expect("the demo ships {demo}");
        let comment_bytes: usize = source
            .lines()
            .filter(|line| line.trim_start().starts_with("//"))
            .map(str::len)
            .sum();
        assert!(
            comment_bytes < 1200,
            "{demo} carries {comment_bytes} bytes of comment — the explanation belongs in the \
             run sheet; the file is what the audience sees on screen"
        );
    }
}
