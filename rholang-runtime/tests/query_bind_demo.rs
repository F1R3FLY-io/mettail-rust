//! CI gate for the **Query Bind** demo (`demos/rholang-query-bind/`).
//!
//! The demo's vehicle is the `rholang` interpreter binary run on committed `.rho` files, so this
//! file drives that binary with the run sheet's own command lines and asserts, per beat, what the
//! audience sees. Without it the run sheet is a hand-run narrative that rots silently — the same
//! reasoning `church_desk_demo.rs` and `lookahead_demo.rs` are built on.
//!
//! ## ★ Why this demo needs a gate more than most
//!
//! `!?` did **nothing** until 2026-07-28 (`ac7f71af`, then `6e6639ee` for the expansion's `Par`
//! ordering). Not "the wrong thing" — nothing: the expansion was computed and discarded, so the
//! lowering read the service channel as an ordinary receive channel, dropped the arguments, and
//! emitted no request send. A receive with no partner is *supposed* to rest, so the defect
//! produced no error, no diagnostic, and exit code zero. **A `.rho` file that publishes nothing
//! looks identical whether the COMM failed or the program never printed.**
//!
//! So a transcript assertion alone would be worth very little here. Four independent claims are
//! asserted instead, and each closes off one way this demo could look convincing while proving
//! nothing:
//!
//! | cell | the reading it refutes |
//! |---|---|
//! | [`every_beat_publishes_its_control`] | "the harness cannot see `@"OUT"` at all" |
//! | [`beat_1_the_closed_desk_publishes_nothing`] | "any `!?` row publishes unconditionally" |
//! | [`no_beat_transcribes_an_answer_it_claims_to_compute`] | "the answer was pasted into the program" |
//! | [`★ deleting the query bind deletes the answer`](removing_the_query_bind_removes_the_answer) | "these assertions would hold with `!?` absent" |
//!
//! The last is the teeth test. It rewrites beat 1 with the `!?` removed — the service channel
//! left in place, so the row degrades to an ordinary receive on a channel nobody sends to — and
//! requires the computed answer to disappear **while the control still fires**. That is the exact
//! pair of readings the original defect lived between.
//!
//! ## Coverage is read off the GRAMMAR, not hand-listed
//!
//! [`beat_2_exercises_every_declared_query_surface`] takes the set of `!?` rules from the language
//! metadata and requires beat 2 to exhibit a row of each. A hand-listed set is precisely what
//! failed in the feature itself: the rewriter's list and its guard's list were each written by
//! hand, each omitted `InputBindQuotedQuery`, and the guard's own documentation named the rule it
//! did not check.
#![cfg(all(
    feature = "rholang-runtime",
    feature = "lambda-runtime",
    feature = "calculator-runtime"
))]

use std::collections::BTreeSet;
use std::path::PathBuf;
use std::process::{Command, Output};

use mettail_languages::rholang::RholangLanguage;
use mettail_runtime::Language;

/// The demo directory, relative to the workspace root.
const DEMO_DIR: &str = "demos/rholang-query-bind";

/// Every committed program the run sheet runs, in beat order.
const PROGRAMS: &[&str] = &[
    "demos/rholang-query-bind/01-round-trip.rho",
    "demos/rholang-query-bind/02-every-surface.rho",
    "demos/rholang-query-bind/03-two-desks.rho",
    "demos/rholang-query-bind/04-sugar-is-its-expansion.rho",
];

/// The control marker each beat publishes through an ordinary send/receive pair, in beat order.
///
/// One per beat rather than one shared string, because the control is *inside* each program and
/// its text is what the presenter reads off the screen.
const CONTROLS: &[&str] = &[
    "the desk is open",
    "four surfaces, one desk",
    "two desks, one join",
    "asked twice, of one desk",
];

/// The workspace root — `rholang-runtime/..`.
fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("the runtime crate has a parent workspace directory")
        .to_path_buf()
}

/// Run the built `rholang` binary on `path`, exactly as the run sheet does.
///
/// ★ `RUST_MIN_STACK` is deliberately **removed from the environment** rather than merely left
/// unset: the harness must reproduce what a presenter at a terminal gets, and
/// [`no_run_sheet_command_line_raises_the_stack`] asserts the sheet carries no prefix. The
/// ambient environment may carry the variable in from an outer `cargo` invocation.
fn rholang(path: &str) -> Output {
    Command::new(env!("CARGO_BIN_EXE_rholang"))
        .current_dir(workspace_root())
        .env_remove("RUST_MIN_STACK")
        .arg(path)
        .output()
        .expect("the rholang binary must run")
}

fn transcript(output: &Output) -> String {
    format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    )
}

/// The observation lines of a transcript, with the `    [n] ` prefix stripped.
///
/// ★ Returned **without their indices**. `@"OUT"` is a multiset and independent branches race to
/// publish, so the index is a rendering artifact of the order the store happened to hold the data
/// in — see [`beat_2_publishes_the_same_set_every_run`], which measures exactly that.
fn observations(rendered: &str) -> Vec<String> {
    rendered
        .lines()
        .filter_map(|line| {
            let trimmed = line.trim_start();
            let rest = trimmed.strip_prefix('[')?;
            let (index, value) = rest.split_once("] ")?;
            index
                .chars()
                .all(|c| c.is_ascii_digit())
                .then(|| value.to_string())
        })
        .collect()
}

/// The observations of one beat, as a sorted set — the run-to-run invariant.
fn observation_set(program: &str) -> Vec<String> {
    let mut values = observations(&transcript(&rholang(program)));
    values.sort();
    values
}

/// A demo program's **program text**: the source with every `//` comment line removed.
///
/// The header comments explain what each answer is, so a grep over the whole file would find
/// every numeral in prose. The claim is about the program.
fn program_without_comments(path: &str) -> String {
    let source = std::fs::read_to_string(workspace_root().join(path))
        .unwrap_or_else(|err| panic!("{path} must be readable: {err}"));
    source
        .lines()
        .filter(|line| !line.trim_start().starts_with("//"))
        .collect::<Vec<_>>()
        .join("\n")
}

/// The run sheet's **shell lines** — every non-empty line inside a fenced code block, trimmed.
///
/// This is the single definition of *"a command the sheet tells a presenter to type"*, and both
/// run-sheet gates are built on it. Working from the fence rather than from patterns makes the
/// prose/command distinction structural instead of heuristic: explaining a retired incantation in
/// a paragraph is free, while putting it in a block a presenter would copy is not.
fn run_sheet_shell_lines() -> Vec<&'static str> {
    let mut inside = false;
    let mut lines = Vec::new();
    for line in run_sheet().lines() {
        let trimmed = line.trim();
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

/// The run sheet, leaked so callers get `&'static str` without threading a lifetime through every
/// gate. It is a few kilobytes read once per test process.
fn run_sheet() -> &'static str {
    Box::leak(
        std::fs::read_to_string(workspace_root().join(DEMO_DIR).join("RUN-SHEET.md"))
            .expect("the run sheet must be readable")
            .into_boxed_str(),
    )
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// The transcripts, beat by beat
// ════════════════════════════════════════════════════════════════════════════════════════════

/// ★ Beat 1 — the round trip publishes a **computed** reply beside its control, and nothing else.
///
/// `42` is `14 * 3`, performed by the reducer at reply time on the private return channel the
/// query minted. Two observations exactly: one more would mean a query answered itself, one fewer
/// that the round trip did not complete.
#[test]
fn beat_1_the_round_trip_publishes_a_computed_reply() {
    let output = rholang(PROGRAMS[0]);
    let rendered = transcript(&output);
    assert!(output.status.success(), "the beat must exit clean:\n{rendered}");
    assert_eq!(
        observation_set(PROGRAMS[0]),
        vec!["⟦\"the desk is open\"⟧".to_string(), "⟦42⟧".to_string()],
        "★ the query bind must deliver `14 * 3` through its PRIVATE return channel, with the \
         control firing beside it in the same run:\n{rendered}"
    );
}

/// Beat 1's third row — a query to a service nothing serves — publishes **nothing**, while the
/// other two rows publish.
///
/// This is the reading the defect hid inside: a receive with no partner is supposed to rest, and
/// resting is silent. Asserting the silence *next to* two firings is what makes the silence
/// evidence rather than an absence of evidence.
#[test]
fn beat_1_the_closed_desk_publishes_nothing() {
    let rendered = transcript(&rholang(PROGRAMS[0]));
    assert!(
        !rendered.contains("A CLOSED DESK ANSWERED"),
        "a query to an unserved channel must REST — publishing here would mean an `!?` row \
         answers itself:\n{rendered}"
    );
    assert_eq!(
        observations(&rendered).len(),
        2,
        "…and exactly the control and the reply must publish:\n{rendered}"
    );
}

/// Beat 2 — the five values, as a set.
///
/// Asserted as a **set** because the four surfaces run independently and `@"OUT"` is a multiset;
/// see [`beat_2_publishes_the_same_set_every_run`] for the measurement that makes this the right
/// invariant to assert.
#[test]
fn beat_2_publishes_one_observation_per_surface() {
    let rendered = transcript(&rholang(PROGRAMS[1]));
    assert_eq!(
        observation_set(PROGRAMS[1]),
        vec![
            "⟦\"four surfaces, one desk\"⟧".to_string(),
            "⟦\"the empty reply arrived\"⟧".to_string(),
            "⟦169⟧".to_string(),
            "⟦42⟧".to_string(),
            "⟦54⟧".to_string(),
        ],
        "★ one observation per `!?` surface — `20 + 22`, `6 * 9`, `13 * 13` computed by the \
         reducer, the empty surface's marker (nothing is bound, so the body running IS the \
         reply), and the control:\n{rendered}"
    );
}

/// ★ Beat 3 — the two replies are **paired by row order**, which is the whole claim.
///
/// The two desks receive the same argument and answer differently, so the list's positions say
/// which reply reached which row. A shared return channel would admit `[1000, 50, …]` equally.
#[test]
fn beat_3_the_two_replies_are_paired_by_row_order() {
    let rendered = transcript(&rholang(PROGRAMS[2]));
    assert_eq!(
        observation_set(PROGRAMS[2]),
        vec!["⟦\"two desks, one join\"⟧".to_string(), "⟦[50, 1000, 1050]⟧".to_string()],
        "★ `[fee, tax, fee + tax]` in ROW order: `500 / 10` first, `500 * 2` second, and their \
         sum computed after the join. `[1000, 50, …]` would mean the two rows shared a return \
         channel:\n{rendered}"
    );
}

/// ★ Beat 4 — the sugar and the hand-written expansion agree, and the **reducer** says so.
///
/// The third element is `*sugar == byhand` evaluated by the machine over the two values it holds,
/// so `true` is a computed verdict rather than a claim in the run sheet.
#[test]
fn beat_4_the_sugar_and_the_hand_written_expansion_agree() {
    let rendered = transcript(&rholang(PROGRAMS[3]));
    assert_eq!(
        observation_set(PROGRAMS[3]),
        vec!["⟦\"asked twice, of one desk\"⟧".to_string(), "⟦[49, 49, true]⟧".to_string()],
        "★ one persistent desk, asked by the sugar and by its hand-written expansion; the \
         equality is decided by the reducer, not by this file:\n{rendered}"
    );
}

/// Every beat publishes its control, so no beat's negative reading can be "the harness saw
/// nothing".
#[test]
fn every_beat_publishes_its_control() {
    assert_eq!(PROGRAMS.len(), CONTROLS.len(), "every beat must name the control it publishes");
    for (program, control) in PROGRAMS.iter().zip(CONTROLS) {
        let rendered = transcript(&rholang(program));
        assert!(
            rendered.contains(&format!("⟦\"{control}\"⟧")),
            "{program} must publish its control {control:?} — without it, every other assertion \
             about this beat could be satisfied by a run that observed nothing:\n{rendered}"
        );
    }
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// ★ The teeth — the demo can fail, in the direction that matters
// ════════════════════════════════════════════════════════════════════════════════════════════

/// ★★ **Deleting the query bind deletes the answer.**
///
/// Beat 1 is rewritten with `!?(14)` removed from the query row — the service channel left in
/// place, so `for(price <- @"quote"!?(14))` degrades to `for(price <- @"quote")`, an ordinary
/// receive on a channel the desk never sends to. The run must then publish the control **and
/// nothing else**.
///
/// This is the cell that makes the rest of the file mean something. Every assertion above is of
/// the form "these values appear"; without this one, none of them establishes that the values
/// appear *because of* `!?`. It is also the precise pair of readings the original defect lived
/// between: the mutated program is, observationally, what the feature did for its whole existence.
#[test]
fn removing_the_query_bind_removes_the_answer() {
    let intact = program_without_comments(PROGRAMS[0]);
    assert!(
        intact.contains(r#"@"quote"!?(14)"#),
        "the mutation's target must be present in the beat, or this cell is vacuous:\n{intact}"
    );
    let source = std::fs::read_to_string(workspace_root().join(PROGRAMS[0]))
        .expect("beat 1 must be readable")
        .replace(r#"@"quote"!?(14)"#, r#"@"quote""#);

    let mutated = std::env::temp_dir().join(format!(
        "mettail-query-bind-teeth-{}-{}.rho",
        std::process::id(),
        line!()
    ));
    std::fs::write(&mutated, source).expect("the mutated beat must be writable");
    let rendered = transcript(&rholang(&mutated.to_string_lossy()));
    let _ = std::fs::remove_file(&mutated);

    let mut values = observations(&rendered);
    values.sort();
    assert_eq!(
        values,
        vec!["⟦\"the desk is open\"⟧".to_string()],
        "★ with the `!?` removed the round trip cannot happen, so ONLY the control may publish. \
         Seeing `⟦42⟧` here would mean the answer reaches `@\"OUT\"` by some route other than the \
         query bind, and every assertion in this file would be measuring that route \
         instead:\n{rendered}"
    );
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// ★ The claim, not the output
// ════════════════════════════════════════════════════════════════════════════════════════════

/// ★★ **No beat contains an answer it claims to compute.**
///
/// Every published number on this page is arithmetic the reducer performed during a round trip.
/// If someone "simplifies" a beat by pasting an answer into it, the demo stops demonstrating
/// anything and this cell says so.
///
/// The comparison is **token-wise**, not by substring: `50` is a substring of `500`, which beat 3
/// legitimately contains as a request argument, so a `contains` test would be red for the wrong
/// reason and would be "fixed" by weakening it.
#[test]
fn no_beat_transcribes_an_answer_it_claims_to_compute() {
    // (beat, the answers it computes, the operands that must still be present)
    let claims: &[(&str, &[&str], &[&str])] = &[
        (PROGRAMS[0], &["42"], &["14", "3"]),
        (PROGRAMS[1], &["42", "54", "169"], &["20", "22", "6", "9", "13"]),
        (PROGRAMS[2], &["50", "1000", "1050"], &["500", "10", "2"]),
        (PROGRAMS[3], &["49"], &["7"]),
    ];
    for (program, answers, operands) in claims {
        let text = program_without_comments(program);
        let tokens: BTreeSet<&str> = text
            .split(|c: char| !c.is_ascii_alphanumeric())
            .filter(|token| !token.is_empty())
            .collect();
        for answer in *answers {
            assert!(
                !tokens.contains(answer),
                "★ {program} must not contain the numeral {answer} — the whole point is that the \
                 reducer COMPUTES it during the round trip:\n{text}"
            );
        }
        // …and the operands ARE present, so the cell cannot pass by the program being empty.
        for operand in *operands {
            assert!(
                tokens.contains(operand),
                "{program} must still contain the operand {operand}, or the assertion above holds \
                 for the wrong reason:\n{text}"
            );
        }
    }
}

/// ★ Every `!?` surface the GRAMMAR declares is exercised by beat 2.
///
/// The covered set is derived, not listed: [`declared_query_rules`] reads the language metadata,
/// and [`surfaces_in`] classifies the rows beat 2 actually contains. Adding a fourth `!?` rule to
/// the grammar fails here until the demo shows it.
#[test]
fn beat_2_exercises_every_declared_query_surface() {
    let declared = declared_query_rules();
    assert!(
        !declared.is_empty(),
        "the census found NO `!?` rules, so this gate is inert — the metadata shape it reads \
         (`TermDef.type_name` / `TermDef.syntax`) must have changed"
    );
    assert_eq!(
        surfaces_in(&program_without_comments(PROGRAMS[1])),
        declared,
        "beat 2 must exhibit one row per DECLARED `!?` surface. Add the missing form to \
         `02-every-surface.rho` (and to its run-sheet table) — do not weaken this gate."
    );
}

/// Every `InputBind` rule whose DECLARED SYNTAX carries `!?(`, read out of the language metadata.
fn declared_query_rules() -> BTreeSet<String> {
    RholangLanguage
        .metadata()
        .terms()
        .iter()
        .filter(|term| term.type_name == "InputBind" && term.syntax.contains("!?("))
        .map(|term| term.name.to_string())
        .collect()
}

/// Classify every `!?` row in `program` by the `InputBind` rule that admits it.
///
/// The three rules differ only in what sits between `for(` and the arrow, so that is what this
/// reads — structurally, rather than by matching a channel name a rename would break:
///
/// | between `for(` and the arrow | rule |
/// |---|---|
/// | nothing | `InputBindEmptyQuery` |
/// | a `@`-led process pattern | `InputBindQuotedQuery` |
/// | a name | `InputBindQuery` |
///
/// A row inside an `&`-join is reached too: the scan restarts at every `for(` **and** every `&`,
/// which are the only two positions a bind may open in.
fn surfaces_in(program: &str) -> BTreeSet<String> {
    let mut found = BTreeSet::new();
    for line in program.lines() {
        for opener in ["for(", "& "] {
            let mut rest = line;
            while let Some(at) = rest.find(opener) {
                let row = &rest[at + opener.len()..];
                rest = row;
                let Some((binder, tail)) = row.split_once("<-") else {
                    continue;
                };
                // Only a row whose CHANNEL side carries `!?(` is a query bind; `tail` stops at
                // the next `&` so a plain row beside a query row is not miscounted.
                let channel = tail.split('&').next().unwrap_or(tail);
                if !channel.contains("!?(") {
                    continue;
                }
                let binder = binder.trim();
                found.insert(
                    match (binder.is_empty(), binder.starts_with('@')) {
                        (true, _) => "InputBindEmptyQuery",
                        (false, true) => "InputBindQuotedQuery",
                        (false, false) => "InputBindQuery",
                    }
                    .to_string(),
                );
            }
        }
    }
    found
}

/// …and the classifier is not vacuous: it recognises each surface in isolation, distinguishes
/// them, and reports **nothing** for an ordinary bind.
///
/// A classifier that answered "all three" for everything would satisfy
/// [`beat_2_exercises_every_declared_query_surface`] no matter what beat 2 contained.
#[test]
fn the_surface_classifier_distinguishes_the_forms_and_ignores_plain_binds() {
    let one = |source: &str| -> Vec<String> { surfaces_in(source).into_iter().collect() };
    assert_eq!(one(r#"for(p <- @"s"!?(1)) { Nil }"#), vec!["InputBindQuery"]);
    assert_eq!(one(r#"for(@p <- @"s"!?(1)) { Nil }"#), vec!["InputBindQuotedQuery"]);
    assert_eq!(one(r#"for(<- @"s"!?(1)) { Nil }"#), vec!["InputBindEmptyQuery"]);
    assert!(
        one(r#"for(@p <- @"s") { Nil }"#).is_empty(),
        "an ordinary bind is not a query bind"
    );
    assert!(
        one(r#"for(@r, @a <- @"s") { @r!(a) }"#).is_empty(),
        "a polyadic ordinary bind is not a query bind either"
    );
    // The `&`-join tail, where a plain head could mask a query row.
    assert_eq!(
        one(r#"for(@a <- @"s" & @b <- @"t"!?(1)) { Nil }"#),
        vec!["InputBindQuotedQuery"]
    );
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// Determinism
// ════════════════════════════════════════════════════════════════════════════════════════════

/// Beats 1, 3 and 4 publish along a single causal chain and settle into exactly one further
/// datum, so their transcripts are **byte-identical** across runs.
///
/// ★ One test per beat rather than a loop: reproducibility of each committed demo is an
/// independent property, the test is nextest's unit of both parallelism and timeout, and the
/// failing beat should be named by the test rather than only by an assertion message.
fn assert_beat_is_byte_reproducible(program: &str) {
    let first = transcript(&rholang(program));
    assert!(
        !observations(&first).is_empty(),
        "{program} produced no observations at all, so comparing runs would compare nothing:\n\
         {first}"
    );
    for run in 2..=3 {
        assert_eq!(
            transcript(&rholang(program)),
            first,
            "{program}: run {run} differed from run 1 — this beat is a single causal chain and \
             must not depend on the scheduler"
        );
    }
}

#[test]
fn beat_1_is_byte_reproducible() {
    assert_beat_is_byte_reproducible(PROGRAMS[0]);
}

#[test]
fn beat_3_is_byte_reproducible() {
    assert_beat_is_byte_reproducible(PROGRAMS[2]);
}

#[test]
fn beat_4_is_byte_reproducible() {
    assert_beat_is_byte_reproducible(PROGRAMS[3]);
}

/// ★ Beat 2's four surfaces are **independent branches**, so its transcript is not byte-stable —
/// its observation SET is.
///
/// Asserted rather than worked around, because it is the honest description of `@"OUT"`: a
/// multiset whose print order is the order the store happened to hold the data in. The run sheet
/// says so in the same words, and a future change that made the order stable would be a change to
/// the reducer worth noticing rather than a silently-passing test.
#[test]
fn beat_2_publishes_the_same_set_every_run() {
    let first = observation_set(PROGRAMS[1]);
    assert_eq!(first.len(), 5, "beat 2 publishes five observations: {first:?}");
    for run in 2..=4 {
        assert_eq!(
            observation_set(PROGRAMS[1]),
            first,
            "beat 2: run {run} published a different SET — the ORDER may move, the values may not"
        );
    }
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// The run sheet cannot drift from the binary
// ════════════════════════════════════════════════════════════════════════════════════════════

/// Every command line the run sheet prints is driven by this file, and every beat this file
/// drives appears in the sheet — so the presenter's page can neither name a command nobody runs
/// nor omit one that is gated.
#[test]
fn every_run_sheet_command_line_is_driven_by_this_test() {
    let shell = run_sheet_shell_lines();
    let invocations: Vec<&str> = shell
        .iter()
        .copied()
        .filter(|line| line.contains("target/debug/rholang"))
        .collect();
    assert!(!invocations.is_empty(), "the run sheet must show how to run the demo");
    for invocation in &invocations {
        assert!(
            PROGRAMS.iter().any(|program| invocation.contains(program)),
            "the run sheet invokes {invocation:?}, which this gate does not drive"
        );
    }
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
/// Prose *about* the retired incantation is wanted and is admitted for free, because
/// [`run_sheet_shell_lines`] yields only what is inside a fence. Inside a fence, any mention of
/// the variable IS a use of it, so this needs no pattern for the spellings.
#[test]
fn no_run_sheet_command_line_raises_the_stack() {
    for line in run_sheet_shell_lines() {
        assert!(
            !line.contains("RUST_MIN_STACK"),
            "the run sheet must not raise the stack — the demos run at the default: {line:?}"
        );
    }
}

/// Every observation the run sheet prints is one the binary produced, and every observation the
/// binary produces is printed in the sheet.
///
/// Both directions, because a sheet that shows a subset of what the audience will see is as
/// misleading as one that shows something they will not.
#[test]
fn the_run_sheet_transcripts_are_the_observed_output() {
    let sheet = run_sheet();
    for program in PROGRAMS {
        for value in observation_set(program) {
            assert!(
                sheet.contains(&value),
                "{program} publishes {value}, which the run sheet never shows"
            );
        }
    }
    // …and the sheet's own observation lines are all accounted for by some beat.
    let published: BTreeSet<String> = PROGRAMS.iter().flat_map(|p| observation_set(p)).collect();
    for line in run_sheet_shell_lines() {
        let Some(rest) = line.strip_prefix('[') else {
            continue;
        };
        let Some((index, value)) = rest.split_once("] ") else {
            continue;
        };
        if !index.chars().all(|c| c.is_ascii_digit()) {
            continue;
        }
        assert!(
            published.contains(value),
            "the run sheet prints the observation {value:?}, which no beat produces"
        );
    }
}
