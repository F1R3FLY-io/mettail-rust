//! **S-D0 — the compile-time guard-discharge gates.**
//!
//! Four gates, plus the golden that records what the corpus actually classifies as.
//!
//! ```text
//!  ┌──────────────────────────────────────────────────────────────────────────────────────┐
//!  │ GATE 1  BYTE-IDENTITY (switch OFF)                                                   │
//!  │   every corpus program lowered with `guard_discharge:false` must produce a `Par`     │
//!  │   byte-identical to the pre-S-D0 compiler's. Proven by encoding the `Par` under      │
//!  │   both switch positions and requiring the OFF bytes to be exactly the bytes the      │
//!  │   unchanged default entry point produced before discharge existed — which, for a     │
//!  │   program with NO dischargeable guard, is also the ON bytes.                         │
//!  ├──────────────────────────────────────────────────────────────────────────────────────┤
//!  │ GATE 2  THE GOLDEN                                                                   │
//!  │   the classification of every corpus guard instance is pinned, one row per site.     │
//!  ├──────────────────────────────────────────────────────────────────────────────────────┤
//!  │ GATE 3  ★ THE NO-LOSS DIFFERENTIAL                                                   │
//!  │   every corpus program RUN on the real f1r3node runtime with the switch ON and with  │
//!  │   it OFF must produce IDENTICAL observed values on EVERY read channel. This is the   │
//!  │   gate that makes discharge a compile-time-only change.                              │
//!  ├──────────────────────────────────────────────────────────────────────────────────────┤
//!  │ GATE 4  EXHAUSTIVENESS                                                               │
//!  │   a new `rhoapi` constructor cannot silently become "closed". Lives with the         │
//!  │   predicate in `rholang-codegen/src/guard_closure.rs`                                │
//!  │   (`a_new_rhoapi_constructor_cannot_silently_become_closed`), because that is where  │
//!  │   the match arms it must break are; asserted here by reference, not duplicated.      │
//!  ├──────────────────────────────────────────────────────────────────────────────────────┤
//!  │ GATE 5  ★ THE RUN-TIME DIFFERENTIAL                                                  │
//!  │   every corpus guard, decided at COMM time by BOTH deciders — f1r3node's `Matcher`   │
//!  │   (rho_pure_eval) and mettail's `SubstrateGuardMatcher` (Dovetail/SFT) — over a      │
//!  │   battery of payloads, through the real `Match::check_commit`. Disagreement in the   │
//!  │   FIRING direction (the substrate commits a COMM the reducer rests on) is a hard     │
//!  │   failure; disagreement in the resting direction is fail-closed and is REPORTED with │
//!  │   its cause, in full, rather than merely counted.                                    │
//!  └──────────────────────────────────────────────────────────────────────────────────────┘
//! ```
//!
//! ## The corpus
//!
//! [`GUARD_CORPUS`] is every distinct `where`-guard instance reachable from the tree's RhoCalc
//! test suites and demos, harvested from:
//!
//! | source | shape |
//! |---|---|
//! | `languages/tests/rhocalc_tests.rs` | the literal guarded programs + the `assert_host_guard` truth-table rows |
//! | `languages/tests/rhocalc_semantic_predicate_ambiguity.rs` | `implies` / `matches` guards |
//! | `rholang-runtime/tests/rho_implies_guard.rs` | the machine-side `implies` rows |
//! | `rholang-runtime/tests/rho_matches_guard.rs` | the `matches` formula rows |
//! | `rholang-runtime/tests/rho_guard_oracle.rs` | the cross-bind `&`-join guards |
//! | `demos/` | the three settlement guards (all payload-dependent) |
//!
//! Each row is `(guard-source, expected-outcome)`. The prediction that motivated S-D0 was
//! ≈29 Discharged/Refuted against ≈72 Residual; the golden records the MEASURED split, and
//! [`the_measured_split_is_recorded`] prints it so a drift is visible in the test log rather
//! than only in a diff.

#![cfg(feature = "rhocalc-runtime")]

use mettail_languages::rhocalc::Proc;
use mettail_rholang_runtime::guard_discharge::{
    guard_as_tagged_continuation, machine_verdict, GuardDischarge,
};
use mettail_rholang_runtime::{
    lower_rhocalc_proc_with_options, run_normalized_par_for_oracle_and_read_runtime_value_channels,
    LoweringOptions,
};
use mettail_runtime::clear_var_cache;
use models::rhoapi::Par;
use prost::Message;
use rspace_plus_plus::rspace::r#match::Match;

// ════════════════════════════════════════════════════════════════════════════════════════════
// The corpus
// ════════════════════════════════════════════════════════════════════════════════════════════

use GuardDischarge::{Discharged, Refuted, Residual};

/// One corpus row: the `where`-guard source, and the outcome `classify` must reach for it.
type GuardRow = (&'static str, GuardDischarge);

/// Every distinct guard instance in the tree's RhoCalc corpus.
///
/// A row's outcome is a fact about the guard ALONE (the receive shape it appears in is
/// irrelevant — `classify` is a pure function of the lowered condition), so each guard is
/// listed once with the canonical single-bind receive used to lower it.
const GUARD_CORPUS: &[GuardRow] = &[
    // ── Constant guards (D0: binder-closed). ────────────────────────────────────────────────
    // `rhocalc_tests.rs:1703,1708` — `assert_never_reaches(… where false …)`.
    ("false", Refuted),
    ("true", Discharged),
    // `rho_matches_guard.rs:142-145` — the logical constants as `matches` formulae are
    // payload-dependent (they mention `x`); the bare constants here are the closed forms.
    ("true and true", Discharged),
    ("true and false", Refuted),
    ("false or true", Discharged),
    ("false or false", Refuted),
    ("not true", Refuted),
    ("not false", Discharged),
    // ── The `implies` truth table (`rhocalc_tests.rs:1417-1420`,
    //    `rho_implies_guard.rs:368,372`). `a implies b` lowers to `EOr(ENot a, b)`. ───────────
    ("false implies false", Discharged),
    ("false implies true", Discharged),
    ("true implies false", Refuted),
    ("true implies true", Discharged),
    // ── The same four rows with COMPARISON operands (`rhocalc_tests.rs:1428-1431`). ──────────
    ("2 > 3 implies 2 > 3", Discharged),
    ("2 > 3 implies 3 > 2", Discharged),
    ("3 > 2 implies 2 > 3", Refuted),
    ("3 > 2 implies 3 > 2", Discharged),
    // ── Precedence rows (`rhocalc_tests.rs:1454-1456`, `rho_implies_guard.rs:261-271`). ──────
    ("false or false implies false and false", Discharged),
    ("true and true implies false or true", Discharged),
    ("true implies false or false", Refuted),
    // ── Closed comparisons. ─────────────────────────────────────────────────────────────────
    ("3 > 2", Discharged),
    ("2 > 3", Refuted),
    ("1 == 1", Discharged),
    ("1 == 2", Refuted),
    // ── Closed COLLECTION comparisons (`rhocalc_tests.rs:3492,3497`). ───────────────────────
    ("Set(1, 2) == Set(2, 1)", Discharged),
    ("Set(1, 2) == Set(1, 3)", Refuted),
    // ── A closed guard that does NOT decide to a boolean (`rho_implies_guard.rs:388`).
    //    `1 implies 2` is `EOr(ENot 1, 2)` — `ENot` on a non-bool is an eval error, so the
    //    machine DECLINES. Residual, never Refuted: refuting would claim knowledge we lack. ──
    ("1 implies 2", Residual),
    ("1", Residual),
    // ── Payload-dependent guards: the overwhelming majority. ────────────────────────────────
    ("x > 0", Residual),
    ("x > 1", Residual),
    ("x > 3", Residual),
    ("x > 10", Residual),
    ("x > 100", Residual),
    ("x > 0 and x > 10", Residual),
    ("x > 0 or x > 10", Residual),
    ("x > 0 implies x > 10", Residual),
    ("x > 0 implies x > 1", Residual),
    ("x > 10 implies x > 100", Residual),
    ("x > 0n", Residual),
    ("x + 1 > 0", Residual),
    ("x == x", Residual), // ← D0′ EXCLUDED: an operational tautology is NOT discharged.
    ("x == 1", Residual),
    ("x == ok", Residual),
    (r#"x == "ok""#, Residual),
    ("x == ok and true", Residual),
    ("x and true", Residual),
    ("x or false", Residual),
    ("not x", Residual),
    ("x implies true", Residual),
    ("true implies x", Residual),
    // ── Spatial (`matches`) guards — the target is always the bound variable. ───────────────
    (r#"x matches @"a"!(1)"#, Residual),
    (r#"x matches @"a"!(2)"#, Residual),
    (r#"x matches @"b"!(1)"#, Residual),
    ("x matches true", Residual),
    // ★ NOT a discharge decision. `lower_proc`'s `Proc::Matches` arm already folds
    // `t matches false` to the constant `false` at `rhocalc_ast.rs:1191` (`is_statically_false`
    // — `Falsum` compiles to `ConnNot(Wildcard)`, the pattern satisfied by NOTHING, so the
    // predicate is false for every `t`), keeping the discarded target's `locally_free` so the
    // free-variable footprint stays conservative. S-D0 then sees an ordinary binder-closed
    // `false` and refutes it. Recorded here because the row looks payload-dependent and is not.
    ("x matches false", Refuted),
    (r#"x matches (@"a"!(1) and true)"#, Residual),
    (r#"x matches (@"a"!(1) and @"z"!(1))"#, Residual),
    (r#"x matches (@"z"!(1) or @"a"!(1))"#, Residual),
    (r#"x matches (@"z"!(1) or @"y"!(1))"#, Residual),
    (r#"x matches (not @"a"!(1))"#, Residual),
    (r#"x matches (not @"z"!(1))"#, Residual),
    (r#"x matches (@"a"!(1) implies @"a"!(1))"#, Residual),
    (r#"x matches (@"a"!(1) implies @"z"!(1))"#, Residual),
    (r#"x matches (@"z"!(1) implies @"z"!(1))"#, Residual),
    (r#"x matches (@"z"!(1) implies @"a"!(1))"#, Residual),
    ("x matches PPar(true, true)", Residual),
    (r#"x matches PPar(@"a"!(1), true)"#, Residual),
    (r#"x matches PPar(@"b"!(2), true)"#, Residual),
    (r#"x matches PPar(@"z"!(9), true)"#, Residual),
    (r#"x matches PPar(@"a"!(1), @"b"!(2))"#, Residual),
    (r#"x matches PPar(@"a"!(1), @"z"!(9))"#, Residual),
    (r#"x matches { @"a"!(1) | true }"#, Residual),
    (r#"x matches { @"z"!(9) | true }"#, Residual),
    (r#"x matches { @"a"!(1) | @"b"!(2) }"#, Residual),
    // ── Guards mixing a closed conjunct with a payload conjunct: still Residual (D0 is
    //    whole-guard closedness; partial folding is NOT built — it would change the
    //    artifact for no measured benefit and is a routing question, not a closedness one). ──
    ("true and x > 0", Residual),
    ("x > 0 and false", Residual),
    ("false or x > 0", Residual),
    // ── ★ THE DEMO GUARDS, VERBATIM (decision U-7: the demos are unchanged by S-D0).
    //    Taken from `demos/rhocalc-settlement/settlement.env` and `RUN-SHEET.md`. All three
    //    are payload-dependent, so all three are Residual and every demo beat behaves
    //    exactly as it did — asserted here rather than argued. ──────────────────────────────
    ("x < 46u32", Residual), // settlement.env `desk`  (`px <= 45u32`, RUN-SHEET §fallback)
    ("100u32 / x >= 1u32", Residual), // RUN-SHEET:131,138 — the divide-by-zero beat
];

/// The cross-bind (`&`-join) corpus: guards over TWO binds. Kept separate because they need a
/// two-bind receive to lower. Every one is payload-dependent by construction.
const JOIN_GUARD_CORPUS: &[GuardRow] = &[
    ("x + y > 10", Residual),                    // rho_guard_oracle.rs:61
    ("y > 1", Residual),                         // rhocalc_tests.rs:1582
    ("y > 10", Residual),                        // rhocalc_tests.rs:1602
    ("x > 1 and y > 1", Residual),               // rhocalc_tests.rs:1819
    ("x > 1 and y > 3", Residual),               // rhocalc_tests.rs:1827
    ("x == y", Residual),                        // rhocalc_tests.rs:3845
    ("x > 1", Residual),                         // rhocalc_tests.rs:1795
    (r#"(x > 1) and (y == "lemon")"#, Residual), // rhocalc_tests.rs:1851
    ("x >= y", Residual),
    ("x != y", Residual),
    // ★ The cross-bind DEMO guard, verbatim from `demos/rhocalc-settlement/settlement.env`'s
    // `settle` row (`px * qty <= 500u32`, in the RUN-SHEET's `<`-fallback spelling). Payload-
    // dependent ⇒ Residual ⇒ the demo is unchanged (decision U-7).
    ("x * y < 501u32", Residual),
];

// ════════════════════════════════════════════════════════════════════════════════════════════
// Harness
// ════════════════════════════════════════════════════════════════════════════════════════════

/// The canonical single-bind guarded receive for a guard expression.
fn single_bind_program(guard: &str) -> String {
    format!(r#"{{ for(x <- c where {guard}){{ out!(*x) }} | c!(2) }}"#)
}

/// The canonical two-bind (`&`-join) guarded receive for a cross-bind guard expression.
fn join_program(guard: &str) -> String {
    format!(r#"{{ for(x <- c1 & y <- c2 where {guard}){{ out!(*x) }} | c1!(2) | c2!(3) }}"#)
}

fn parse(source: &str) -> Proc {
    clear_var_cache();
    Proc::parse_via_wpda(source)
        .unwrap_or_else(|err| panic!("rhocalc parse failed for {source:?}: {err:?}"))
}

fn lower_parsed(proc: &Proc, options: LoweringOptions, source: &str) -> Par {
    lower_rhocalc_proc_with_options(proc, options)
        .unwrap_or_else(|err| panic!("rhocalc lowering failed for {source:?}: {err:?}"))
}

fn lower(source: &str, options: LoweringOptions) -> Par {
    lower_parsed(&parse(source), options, source)
}

/// Lower ONE parsed `Proc` under both switch positions, returning `(discharge-ON, OFF)`.
///
/// ★ CONTROLLED EXPERIMENT — parse once, lower twice. `Proc::PPar` carries its branches in a
/// `HashBag`, whose iteration order is a property of the individual `HashMap` instance, so two
/// SEPARATE parses of the same source can emit the same parallel composition with its top-level
/// `sends` in different orders. That is a pre-existing property of the lowering (a `Par`'s
/// slots are multisets; f1r3node canonically sorts before hashing), entirely independent of
/// S-D0 — but it means comparing bytes across two parses measures the wrong thing. Lowering the
/// SAME `Proc` value twice holds the branch order fixed and leaves `guard_discharge` as the
/// single independent variable, which is exactly what the byte-identity gate must isolate.
fn lower_both(source: &str) -> (Par, Par) {
    let proc = parse(source);
    let on = lower_parsed(&proc, LoweringOptions::PRODUCTION, source);
    let off = lower_parsed(&proc, LoweringOptions::NO_DISCHARGE, source);
    (on, off)
}

/// The `Receive.condition` of the (single) receive in `par`, if it survived lowering.
fn receive_condition(par: &Par) -> Option<Par> {
    par.receives
        .first()
        .and_then(|receive| receive.condition.clone())
}

/// The outcome S-D0 reached for `guard`, READ OFF THE ARTIFACT rather than recomputed: the
/// condition is present under `NO_DISCHARGE` and absent under `PRODUCTION` iff it discharged.
///
/// Reading the artifact (rather than calling `classify` again) is what makes this a gate on the
/// COMPILER rather than a gate on a function the compiler might not be calling.
fn outcome_from_artifact(program: &str) -> GuardDischarge {
    let (on, off) = lower_both(program);
    let off_cond = receive_condition(&off)
        .unwrap_or_else(|| panic!("discharge-OFF lowering of {program:?} lost its guard"));
    match receive_condition(&on) {
        None => GuardDischarge::Discharged,
        Some(on_cond) => {
            assert_eq!(
                on_cond, off_cond,
                "a NON-discharged guard must be emitted VERBATIM under both switch positions \
                 ({program:?})"
            );
            // Refuted and Residual are artifact-identical by design (decision U-3): a
            // never-firing `for` is a resting observable, so refutation only ever raises a
            // diagnostic. Distinguish them by the verdict the machine reaches on the condition.
            match machine_verdict(&off_cond) {
                Some(false) if mettail_rholang_runtime::is_binder_closed(&off_cond) => {
                    GuardDischarge::Refuted
                },
                _ => GuardDischarge::Residual,
            }
        },
    }
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// GATE 2 — the golden
// ════════════════════════════════════════════════════════════════════════════════════════════

/// Every corpus guard classifies exactly as the golden says, READ OFF THE EMITTED ARTIFACT.
#[test]
fn the_guard_corpus_golden() {
    let mut mismatches = Vec::new();
    for (guard, expected) in GUARD_CORPUS {
        let actual = outcome_from_artifact(&single_bind_program(guard));
        if actual != *expected {
            mismatches.push(format!("  {guard:?}: expected {expected:?}, got {actual:?}"));
        }
    }
    for (guard, expected) in JOIN_GUARD_CORPUS {
        let actual = outcome_from_artifact(&join_program(guard));
        if actual != *expected {
            mismatches.push(format!("  (join) {guard:?}: expected {expected:?}, got {actual:?}"));
        }
    }
    assert!(
        mismatches.is_empty(),
        "guard-discharge golden drifted on {} row(s):\n{}",
        mismatches.len(),
        mismatches.join("\n")
    );
}

/// The MEASURED split, printed so drift is visible in the log and not only in a diff.
///
/// The S-D0 design predicted ≈29 Discharged+Refuted against ≈72 Residual over ≈101 instances.
#[test]
fn the_measured_split_is_recorded() {
    let (mut discharged, mut refuted, mut residual) = (0usize, 0usize, 0usize);
    let rows = GUARD_CORPUS
        .iter()
        .map(|(g, e)| (single_bind_program(g), *e))
        .chain(JOIN_GUARD_CORPUS.iter().map(|(g, e)| (join_program(g), *e)));
    for (program, _) in rows {
        match outcome_from_artifact(&program) {
            GuardDischarge::Discharged => discharged += 1,
            GuardDischarge::Refuted => refuted += 1,
            GuardDischarge::Residual => residual += 1,
        }
    }
    let total = discharged + refuted + residual;
    println!(
        "S-D0 measured corpus split: {total} guard instances = {discharged} Discharged \
         + {refuted} Refuted ({} statically decided) + {residual} Residual",
        discharged + refuted
    );
    assert_eq!(total, GUARD_CORPUS.len() + JOIN_GUARD_CORPUS.len());
    // The design's load-bearing claims, asserted rather than merely printed:
    assert!(discharged > 0, "at least one guard must actually discharge, else S-D0 is inert");
    assert!(
        residual > discharged + refuted,
        "the corpus is dominated by payload-dependent guards; a majority of statically decided \
         guards would mean the classifier is over-firing"
    );
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// GATE 1 — byte-identity with the switch OFF
// ════════════════════════════════════════════════════════════════════════════════════════════

/// ★ With `guard_discharge:false`, the emitted `Par` is BYTE-IDENTICAL to the pre-S-D0
/// compiler's for every corpus program.
///
/// Proven structurally rather than against a stored blob: S-D0 touches exactly one expression
/// in the lowering, and that expression is a no-op when the switch is off
/// (`(_, condition) => condition`). The observable consequence is that the OFF artifact still
/// carries every guard verbatim, and that the ON and OFF artifacts differ ONLY by the presence
/// of a discharged `Receive.condition` — i.e. for a program with no dischargeable guard the two
/// encodings are equal byte for byte. Both halves are asserted here over the whole corpus.
#[test]
fn switch_off_emits_every_guard_verbatim_and_matches_on_where_nothing_discharges() {
    let mut identical = 0usize;
    let mut differing = 0usize;
    let programs = GUARD_CORPUS
        .iter()
        .map(|(g, _)| single_bind_program(g))
        .chain(JOIN_GUARD_CORPUS.iter().map(|(g, _)| join_program(g)));
    for program in programs {
        let (on, off) = lower_both(&program);

        // Half 1: the OFF artifact NEVER loses a guard.
        assert!(
            receive_condition(&off).is_some(),
            "discharge-OFF must emit every guard verbatim; {program:?} lost its condition"
        );

        // Half 2: ON and OFF are byte-identical exactly when nothing discharged.
        let off_bytes = off.encode_to_vec();
        let on_bytes = on.encode_to_vec();
        match receive_condition(&on).is_some() {
            true => {
                assert_eq!(
                    on_bytes, off_bytes,
                    "a non-discharged program must encode identically under both switch \
                     positions: {program:?}"
                );
                identical += 1;
            },
            false => {
                assert_ne!(
                    on_bytes, off_bytes,
                    "a DISCHARGED program must differ from its non-discharged encoding: \
                     {program:?}"
                );
                differing += 1;
            },
        }
    }
    println!(
        "S-D0 byte-identity: {identical} program(s) byte-identical ON/OFF, \
         {differing} program(s) differ solely by the discharged condition"
    );
    assert!(differing > 0, "no program discharged — the gate would be vacuous");
}

/// The discharged form is `None`, NEVER `Some(Par::default())`. The empty-`Par` form is a
/// DIFFERENT artifact that `reduce.rs` merely happens to collapse; an artifact difference is a
/// consensus difference.
#[test]
fn a_discharged_condition_is_absent_not_empty() {
    let par = lower(&single_bind_program("true"), LoweringOptions::PRODUCTION);
    let receive = par.receives.first().expect("the program has a receive");
    assert_eq!(receive.condition, None, "discharge must set `condition = None`");
    assert_ne!(
        receive.condition,
        Some(Par::default()),
        "the empty-`Par` guard form is a different artifact and must not be emitted"
    );
}

/// ★ Discharging must not disturb `locally_free`. The decision site sits BEFORE the
/// `locally_free` union precisely so the receive never carries bits contributed by a condition
/// that is no longer in the emitted `Par`.
#[test]
fn a_discharged_receive_carries_no_bits_from_its_vanished_guard() {
    // A closed guard contributes NO free bits either way, so ON and OFF must agree exactly …
    for guard in ["true", "3 > 2", "false implies true"] {
        let (on, off) = lower_both(&single_bind_program(guard));
        assert_eq!(
            on.receives[0].locally_free, off.receives[0].locally_free,
            "a binder-closed guard contributes no free bits; discharging it must not change \
             `locally_free` for {guard:?}"
        );
        assert_eq!(
            on.locally_free, off.locally_free,
            "top-level `locally_free` must be unchanged by discharge for {guard:?}"
        );
    }
    // … and the receive's own bitset must never mention a bit the emitted term cannot justify.
    let on = lower(&single_bind_program("true"), LoweringOptions::PRODUCTION);
    assert!(
        on.receives[0].condition.is_none(),
        "precondition: this program's guard discharges"
    );
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// GATE 3 — ★ the no-loss differential
// ════════════════════════════════════════════════════════════════════════════════════════════

/// The channels every differential program is read back on.
const READ_CHANNELS: &[&str] = &["out", "c", "c1", "c2"];

/// ★ THE NO-LOSS DIFFERENTIAL. Every corpus program, RUN on the real f1r3node runtime under
/// both switch positions, produces IDENTICAL observed values on EVERY read channel.
///
/// This is the gate that makes discharge a compile-time-only change: not "the artifact differs
/// only here", but "the OBSERVABLE BEHAVIOUR does not differ at all". It covers the firing
/// COMMs (a discharged guard must still fire), the blocked ones (a refuted guard must still
/// leave its datum resting), and the residual majority (unchanged by construction).
#[tokio::test(flavor = "multi_thread")]
async fn running_on_and_off_observes_identical_values_on_every_channel() {
    let programs: Vec<String> = GUARD_CORPUS
        .iter()
        .map(|(g, _)| single_bind_program(g))
        .chain(JOIN_GUARD_CORPUS.iter().map(|(g, _)| join_program(g)))
        .collect();

    let mut divergences = Vec::new();
    for program in &programs {
        let (on, off) = lower_both(program);

        let on_observed =
            run_normalized_par_for_oracle_and_read_runtime_value_channels(&on, READ_CHANNELS)
                .await
                .unwrap_or_else(|err| panic!("discharge-ON run failed for {program:?}: {err}"));
        let off_observed =
            run_normalized_par_for_oracle_and_read_runtime_value_channels(&off, READ_CHANNELS)
                .await
                .unwrap_or_else(|err| panic!("discharge-OFF run failed for {program:?}: {err}"));

        for channel in READ_CHANNELS {
            let on_values = on_observed.get(*channel);
            let off_values = off_observed.get(*channel);
            if on_values != off_values {
                divergences.push(format!(
                    "  {program:?} channel {channel:?}: ON={on_values:?} OFF={off_values:?}"
                ));
            }
        }
    }
    assert!(
        divergences.is_empty(),
        "★ NO-LOSS DIFFERENTIAL VIOLATED — discharge changed observable behaviour on {} \
         program/channel pair(s):\n{}",
        divergences.len(),
        divergences.join("\n")
    );
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// The soundness core, against the REAL runtime entry point
// ════════════════════════════════════════════════════════════════════════════════════════════

/// ★ For every corpus guard, the compile-time verdict coincides with what f1r3node's own
/// `Matcher::check_commit` answers on the same condition with NO bindings.
///
/// Discharge is exactly the claim "`check_commit` would have returned `true`, so omitting the
/// guard — which makes `check_commit` return `true` by short-circuit — changes nothing". This
/// test drives that claim through the real function rather than a re-implementation of it, and
/// therefore also pins the private `extract_bool` this crate had to reproduce.
#[test]
fn machine_verdict_agrees_with_the_runtime_check_commit() {
    let matcher = rholang::rust::interpreter::matcher::r#match::Matcher;
    let mut checked = 0usize;
    for (guard, _) in GUARD_CORPUS {
        let off = lower(&single_bind_program(guard), LoweringOptions::NO_DISCHARGE);
        let condition = receive_condition(&off).expect("OFF keeps every guard");
        if !mettail_rholang_runtime::is_binder_closed(&condition) {
            continue; // `check_commit` with no bindings is only meaningful for a closed guard
        }
        let tc = guard_as_tagged_continuation(&condition);
        assert_eq!(
            machine_verdict(&condition) == Some(true),
            matcher.check_commit(&tc, &[]),
            "compile-time verdict must equal the runtime `check_commit` verdict for {guard:?}"
        );
        checked += 1;
    }
    assert!(checked > 0, "no binder-closed guard reached the runtime agreement check");
    println!(
        "S-D0 runtime agreement: {checked} binder-closed corpus guard(s) checked against \
              `Matcher::check_commit`"
    );
}

/// ★ THE ANTI-DIVERGENCE FENCE, over the corpus: for every binder-closed guard, the HOST
/// evaluator and the MACHINE evaluator must reach the same verdict.
///
/// A row that fails here is a **divergence-A-shaped finding** — two evaluators of the same
/// surface guard language disagreeing on a condition with no free variables. The production
/// path already handles it safely (`classify` falls to `Residual` and logs at `WARN`), but it
/// must be surfaced, not absorbed, so it is a hard failure here.
#[test]
fn the_two_evaluators_agree_on_every_binder_closed_corpus_guard() {
    let mut disagreements = Vec::new();
    let mut checked = 0usize;
    for (guard, _) in GUARD_CORPUS {
        let program = single_bind_program(guard);
        clear_var_cache();
        let proc = Proc::parse_via_wpda(&program)
            .unwrap_or_else(|err| panic!("parse failed for {program:?}: {err:?}"));
        let par = mettail_rholang_runtime::lower_rhocalc_proc_with_options(
            &proc,
            LoweringOptions::NO_DISCHARGE,
        )
        .unwrap_or_else(|err| panic!("lowering failed for {program:?}: {err:?}"));
        let Some(condition) = receive_condition(&par) else {
            continue;
        };
        if !mettail_rholang_runtime::is_binder_closed(&condition) {
            continue;
        }
        checked += 1;
        let machine = machine_verdict(&condition);
        let host = host_verdict_for(&proc);
        match (machine, host) {
            (Some(m), Some(h)) if m != h => disagreements
                .push(format!("  {guard:?}: machine={m}, host={h}  ← DIVERGENCE-A-SHAPED")),
            _ => {},
        }
    }
    assert!(checked > 0, "no binder-closed guard reached the fence check");
    assert!(
        disagreements.is_empty(),
        "★ GUARD EVALUATOR DISAGREEMENT on {} binder-closed guard(s). The machine \
         (rho_pure_eval + SpatialMatcherOracle) and the host front-end evaluator read the same \
         guard differently:\n{}",
        disagreements.len(),
        disagreements.join("\n")
    );
    println!("S-D0 fence: {checked} binder-closed corpus guard(s), 0 evaluator disagreements");
}

/// Pull the `where`-guard `Proc` back out of a parsed program and ask the HOST evaluator.
///
/// The two guard-bearing `ForRow` arms are enumerated explicitly (no wildcard for a *guard*
/// arm), so a new `…Where` variant is a visible gap here rather than a silently skipped row.
fn host_verdict_for(proc: &Proc) -> Option<bool> {
    fn guard_of(proc: &Proc) -> Option<&Proc> {
        match proc {
            Proc::PForUser(rows, _) => rows.iter().find_map(for_row_guard),
            Proc::PPar(branches) => branches.iter().find_map(|(branch, _)| guard_of(branch)),
            _ => None,
        }
    }
    fn for_row_guard(row: &mettail_languages::rhocalc::ForRow) -> Option<&Proc> {
        use mettail_languages::rhocalc::ForRow as R;
        match row {
            R::ForRowWhere(_, _, cond) | R::ForRowSingleWhere(_, cond) => Some(cond.as_ref()),
            _ => None,
        }
    }
    guard_of(proc).and_then(mettail_languages::rhocalc::receive::eval_guard_bool)
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// The three CONSTRUCTED guard sites: 0% dischargeable, asserted not assumed
// ════════════════════════════════════════════════════════════════════════════════════════════

/// `rholang-codegen`'s three guard-CONSTRUCTING sites — `rho_net_flt::flt_receive_par`'s
/// linearity guards, `rho_net_lower`'s `ac_nonlinear_condition` and
/// `nonlinear_consistency_condition` — all build `EEq(BoundVar_i, BoundVar_j)` conjunctions
/// over the receiver's OWN formals. Payload-dependent by construction ⇒ 0% dischargeable.
///
/// The sites themselves carry `debug_assert!(!is_binder_closed(..))` in-crate (assert only,
/// never branch); this test pins the full `classify(..) == Residual` verdict, which
/// additionally needs the evaluator and therefore cannot live in `rholang-codegen`.
#[test]
fn the_three_codegen_guard_sites_are_all_residual() {
    use mettail_rholang_runtime::guard_discharge::{classify, GuardRouting};
    use models::create_bit_vector;
    use models::rhoapi::expr::ExprInstance;
    use models::rhoapi::{EAnd, EEq, Expr};
    use models::rust::utils::new_boundvar_par;

    fn expr_par(instance: ExprInstance) -> Par {
        Par {
            exprs: vec![Expr { expr_instance: Some(instance) }],
            ..Par::default()
        }
    }
    fn slot_eq(i: usize, j: usize) -> Par {
        expr_par(ExprInstance::EEqBody(EEq {
            p1: Some(new_boundvar_par(i as i32, create_bit_vector(&[i]), false)),
            p2: Some(new_boundvar_par(j as i32, create_bit_vector(&[j]), false)),
        }))
    }

    // The exact three shapes: a single conjunct, a two-conjunct `EAnd`, and a three-conjunct
    // left-nested `EAnd` (the shape all three sites fold into).
    let single = slot_eq(2, 0);
    let pair = expr_par(ExprInstance::EAndBody(EAnd {
        p1: Some(slot_eq(3, 1)),
        p2: Some(slot_eq(2, 0)),
    }));
    let triple = expr_par(ExprInstance::EAndBody(EAnd {
        p1: Some(pair.clone()),
        p2: Some(slot_eq(4, 1)),
    }));

    for (name, cond) in [("single", single), ("pair", pair), ("triple", triple)] {
        assert!(
            !mettail_rholang_runtime::is_binder_closed(&cond),
            "{name}: an EEq-over-formals guard must never be binder-closed"
        );
        assert_eq!(
            classify(Some(true), &cond, GuardRouting::MachineEvaluated),
            GuardDischarge::Residual,
            "{name}: a constructed non-linearity guard must be Residual even if a host leg \
             claimed `true`"
        );
    }
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// Demo fidelity (decisions U-7 and the optional Beat 3b)
// ════════════════════════════════════════════════════════════════════════════════════════════

/// ★ The RUN-SHEET's **Beat 3b** claims, VERIFIED rather than asserted on paper.
///
/// The two programs are copied verbatim from
/// `demos/rhocalc-settlement/RUN-SHEET.md`. Beat 3b tells the audience three things, and all
/// three are checked here: the vacuous guard fires, its `where` clause is ABSENT from the
/// compiled artifact, and the statically-false mirror neither fires nor loses its guard.
#[tokio::test(flavor = "multi_thread")]
async fn the_run_sheets_beat_3b_is_exactly_what_the_compiler_does() {
    // ── Claim 1: `false implies false` is vacuously true, so the receive commits … ──────────
    let vacuous = r#"{ for(@px <- @("offer") where false implies false){@("OUT")!(px)}
                       | @("offer")!(42u32) }"#;
    let (on, off) = lower_both(vacuous);

    // ── Claim 2: … and its `where` clause is not in the artifact at all. ────────────────────
    assert!(
        receive_condition(&on).is_none(),
        "Beat 3b: the vacuous guard must be DISCHARGED — no `Receive.condition` is emitted"
    );
    assert!(
        receive_condition(&off).is_some(),
        "…and the switch-off arm must still carry it, so the two arms are comparable"
    );

    let on_values =
        run_normalized_par_for_oracle_and_read_runtime_value_channels(&on, &["OUT", "offer"])
            .await
            .expect("Beat 3b vacuous-guard run (discharge ON)");
    let off_values =
        run_normalized_par_for_oracle_and_read_runtime_value_channels(&off, &["OUT", "offer"])
            .await
            .expect("Beat 3b vacuous-guard run (discharge OFF)");
    assert_eq!(
        on_values.get("OUT").map(Vec::len),
        Some(1),
        "Beat 3b: `OUT: [42] (1 value(s))` — the vacuous guard commits; got {on_values:?}"
    );
    assert_eq!(
        on_values, off_values,
        "Beat 3b: discharging the guard must not change a single observation"
    );

    // ── Claim 3: the statically-FALSE mirror does not fire, and KEEPS its guard. ────────────
    let refuted = r#"{ for(@px <- @("offer") where true implies false){@("OUT")!(px)}
                       | @("offer")!(42u32) }"#;
    let (on, off) = lower_both(refuted);
    assert!(
        receive_condition(&on).is_some(),
        "Beat 3b: a statically-FALSE guard is REPORTED, never removed — a `for` that can \
         never fire is a resting observable"
    );
    assert_eq!(
        on.encode_to_vec(),
        off.encode_to_vec(),
        "Beat 3b: refutation leaves the artifact byte-identical"
    );
    let observed =
        run_normalized_par_for_oracle_and_read_runtime_value_channels(&on, &["OUT", "offer"])
            .await
            .expect("Beat 3b refuted-guard run");
    assert_eq!(
        observed.get("OUT").map(Vec::len).unwrap_or(0),
        0,
        "Beat 3b: `OUT: [] (0 value(s))` — the refuted guard never commits; got {observed:?}"
    );
    assert_eq!(
        observed.get("offer").map(Vec::len),
        Some(1),
        "…and the offer is STILL RESTING, which is why the receive may not be folded away"
    );
}

/// ★ Decision U-7: the demos are UNCHANGED by S-D0. Every settlement guard, taken verbatim
/// from `demos/rhocalc-settlement/settlement.env` and its RUN-SHEET, is payload-dependent and
/// therefore Residual — the compiled demo is byte-identical with the switch either way.
#[test]
fn every_settlement_demo_guard_is_residual_so_the_demo_is_unchanged() {
    let demo_guards = [
        ("x < 46u32", "the `desk` limit order"),
        ("x * y < 501u32", "the `settle` cross-channel budget"),
        ("100u32 / x >= 1u32", "the SafeArith divide-by-zero veto"),
        ("x + y < 60u32", "the RUN-SHEET's Beat-4 budget fallback"),
    ];
    for (guard, what) in demo_guards {
        let program = match guard.contains('y') {
            true => join_program(guard),
            false => single_bind_program(guard),
        };
        assert_eq!(
            outcome_from_artifact(&program),
            GuardDischarge::Residual,
            "{what} ({guard:?}) is payload-dependent and must stay on the machine"
        );
        let (on, off) = lower_both(&program);
        assert_eq!(
            on.encode_to_vec(),
            off.encode_to_vec(),
            "{what}: the demo artifact must be byte-identical under both switch positions"
        );
    }
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// GATE 4 — exhaustiveness (asserted by reference)
// ════════════════════════════════════════════════════════════════════════════════════════════

// ════════════════════════════════════════════════════════════════════════════════════════════
// GATE 5 — ★ THE RUN-TIME DIFFERENTIAL: the two COMM-time guard deciders, over the corpus
// ════════════════════════════════════════════════════════════════════════════════════════════

/// The payload battery a single-bind corpus guard is decided against.
///
/// The corpus programs bind `x` to `2`, but a differential over one payload measures almost
/// nothing: the interesting rows are the ones where an operand leaves the decidable fragment
/// (a sort mismatch, an overflow, a process-shaped value). Each row is therefore decided against
/// every payload below, and a payload that makes the guard nonsense is *kept* — "both deciders
/// refuse it" is exactly what has to be shown.
fn single_bind_payload_battery() -> Vec<(&'static str, Vec<Par>)> {
    use models::rhoapi::{EList, Send};
    use models::rust::utils::{new_gbool_par, new_gint_par, new_gstring_par};
    let int = |n: i64| new_gint_par(n, Vec::new(), false);
    let list = Par::default().with_exprs(vec![models::rhoapi::Expr {
        expr_instance: Some(models::rhoapi::expr::ExprInstance::EListBody(EList {
            ps: vec![int(1), int(2)],
            locally_free: Vec::new(),
            connective_used: false,
            remainder: None,
        })),
    }]);
    let process = Par::default().with_sends(vec![Send {
        chan: Some(new_gstring_par("a".to_string(), Vec::new(), false)),
        data: vec![int(1)],
        persistent: false,
        locally_free: Vec::new(),
        connective_used: false,
    }]);
    let double = Par::default().with_exprs(vec![models::rust::utils::new_gdouble_expr(1.5)]);
    let bigint = Par::default().with_exprs(vec![models::rust::utils::new_gbigint_expr(vec![0x00])]);
    vec![
        ("x=2 (the program's own payload)", vec![int(2)]),
        ("x=0", vec![int(0)]),
        ("x=-1", vec![int(-1)]),
        ("x=101", vec![int(101)]),
        ("x=40000 (past the substrate's 16-bit static domain)", vec![int(40_000)]),
        ("x=i64::MAX", vec![int(i64::MAX)]),
        ("x=i64::MIN", vec![int(i64::MIN)]),
        ("x=true", vec![new_gbool_par(true, Vec::new(), false)]),
        ("x=false", vec![new_gbool_par(false, Vec::new(), false)]),
        ("x=\"ok\"", vec![new_gstring_par("ok".to_string(), Vec::new(), false)]),
        (
            "x=\"OK\" (case differs)",
            vec![new_gstring_par("OK".to_string(), Vec::new(), false)],
        ),
        ("x=\"\" (empty)", vec![new_gstring_par(String::new(), Vec::new(), false)]),
        ("x=1.5 (double)", vec![double]),
        ("x=0n (big integer)", vec![bigint]),
        ("x=[1,2]", vec![list]),
        ("x=@\"a\"!(1) (process-shaped)", vec![process]),
        ("x=<no payload at all>", vec![]),
    ]
}

/// The cross-bind battery: the two binds' payloads, concatenated in receive-bind order.
fn join_payload_battery() -> Vec<(&'static str, Vec<Par>)> {
    use models::rust::utils::{new_gbool_par, new_gint_par, new_gstring_par};
    let int = |n: i64| new_gint_par(n, Vec::new(), false);
    vec![
        ("x=2, y=3 (the program's own payloads)", vec![int(2), int(3)]),
        ("x=3, y=2", vec![int(3), int(2)]),
        ("x=0, y=0", vec![int(0), int(0)]),
        ("x=i64::MAX, y=1", vec![int(i64::MAX), int(1)]),
        ("x=1, y=i64::MIN", vec![int(1), int(i64::MIN)]),
        (
            "x=\"lemon\", y=\"lemon\"",
            vec![
                new_gstring_par("lemon".to_string(), Vec::new(), false),
                new_gstring_par("lemon".to_string(), Vec::new(), false),
            ],
        ),
        (
            "x=true, y=false",
            vec![new_gbool_par(true, Vec::new(), false), new_gbool_par(false, Vec::new(), false)],
        ),
        (
            "x=2, y=\"lemon\" (mixed sorts)",
            vec![int(2), new_gstring_par("lemon".to_string(), Vec::new(), false)],
        ),
        ("x=2 (only ONE bind arrived)", vec![int(2)]),
    ]
}

/// Drive one decider through the REAL `Match::check_commit` entry point.
fn commit_verdict(
    matcher: &dyn Match<
        models::rhoapi::BindPattern,
        models::rhoapi::ListParWithRandom,
        models::rhoapi::TaggedContinuation,
    >,
    condition: &Par,
    payloads: &[Par],
) -> bool {
    let matched = models::rhoapi::ListParWithRandom {
        pars: payloads.to_vec(),
        random_state: Vec::new(),
    };
    matcher.check_commit(&guard_as_tagged_continuation(condition), &[&matched])
}

/// Why the substrate could not decide a guard, read off the encoding rather than guessed.
///
/// The three causes are the three refusals in
/// `guard_par_substrate::substrate_guard_verdict`, in the order it applies them.
fn undecided_cause(condition: &Par, payloads: &[Par]) -> String {
    use mettail_rholang_runtime::guard_par_substrate::{encode_par_guard, substitute_bound_pars};
    let substituted = substitute_bound_pars(condition, payloads);
    let encoding = encode_par_guard(&substituted);
    match encoding.vars.is_empty() {
        false => {
            return format!(
                "RESIDUAL BINDER — {} slot(s) the substitution could not reach",
                encoding.vars.len()
            )
        },
        true => {},
    }
    for (index, fragment) in encoding.opaque.iter().enumerate() {
        if machine_verdict(fragment).is_none() {
            let kind = encoding
                .formula
                .atoms()
                .into_iter()
                .find(|atom| atom.id as usize == index)
                .map(|atom| format!("{:?}", atom.kind))
                .unwrap_or_else(|| "collapsed out of the formula".to_string());
            return format!("UNDECIDABLE FRAGMENT #{index} ({kind})");
        }
    }
    "SUBSTRATE-UNDECIDED LEAF (outside the decided fragment)".to_string()
}

/// ★ **GATE 5 — THE RUN-TIME DIFFERENTIAL.**
///
/// Every corpus guard, at COMM time, decided by both deciders over the payload battery. The
/// substrate is allowed to be *more* conservative than the reducer — an undecided guard fails
/// closed, leaving the datum resting and observable — but it may **never** commit a COMM the
/// reducer rests on. The first direction is reported in full; the second fails the gate.
#[test]
fn the_two_comm_time_deciders_agree_on_the_whole_corpus() {
    let reducer = rholang::rust::interpreter::matcher::r#match::Matcher;
    let substrate = mettail_rholang_runtime::guard_par_substrate::SubstrateGuardMatcher::new();

    let mut comparisons = 0usize;
    let mut fail_closed = Vec::new();
    let mut fires_where_reducer_rests = Vec::new();

    let rows = GUARD_CORPUS
        .iter()
        .map(|(guard, _)| (*guard, single_bind_program(guard), single_bind_payload_battery()))
        .chain(
            JOIN_GUARD_CORPUS
                .iter()
                .map(|(guard, _)| (*guard, join_program(guard), join_payload_battery())),
        );

    for (guard, program, battery) in rows {
        let lowered = lower(&program, LoweringOptions::NO_DISCHARGE);
        let condition = receive_condition(&lowered)
            .unwrap_or_else(|| panic!("discharge-OFF lowering of {program:?} lost its guard"));
        for (payload_label, payloads) in battery {
            comparisons += 1;
            let reducer_says = commit_verdict(&reducer, &condition, &payloads);
            let substrate_says = commit_verdict(&substrate, &condition, &payloads);
            match (reducer_says, substrate_says) {
                (true, true) | (false, false) => {},
                (true, false) => fail_closed.push(format!(
                    "  {guard:?} [{payload_label}]: reducer=true substrate=false — {}",
                    undecided_cause(&condition, &payloads)
                )),
                (false, true) => fires_where_reducer_rests
                    .push(format!("  {guard:?} [{payload_label}]: reducer=false substrate=TRUE")),
            }
        }
    }

    println!(
        "★ GATE 5 run-time differential: {comparisons} (guard × payload) comparisons, \
         {} fail-closed disagreement(s), {} firing-direction disagreement(s)",
        fail_closed.len(),
        fires_where_reducer_rests.len()
    );
    for row in &fail_closed {
        println!("{row}");
    }

    assert!(
        fires_where_reducer_rests.is_empty(),
        "★ NOT FAIL-CLOSED — the substrate commits a COMM the reducer rests on, in {} \
         comparison(s):\n{}",
        fires_where_reducer_rests.len(),
        fires_where_reducer_rests.join("\n")
    );
    assert_eq!(
        fail_closed.len(),
        0,
        "the substrate refused {} guard(s) the reducer commits. Each is fail-closed and \
         therefore safe, but the set is PINNED so a widening is visible here rather than only \
         in behaviour:\n{}",
        fail_closed.len(),
        fail_closed.join("\n")
    );
}

/// Gate 4 lives with the predicate it protects, in
/// `rholang-codegen/src/guard_closure.rs::a_new_rhoapi_constructor_cannot_silently_become_closed`
/// — a match over every `ExprInstance` / `VarInstance` / `ConnectiveInstance` variant with NO
/// wildcard arm, so adding a constructor to `rhoapi` is a compile error there.
///
/// This test records the dependency so the gate cannot be deleted unnoticed: it exercises the
/// re-exported predicate on the two ends of the lattice a new constructor would land between.
#[test]
fn gate_4_exhaustiveness_is_enforced_at_the_predicate() {
    use models::rust::utils::{new_gbool_par, new_wildcard_par};
    assert!(mettail_rholang_runtime::is_binder_closed(&new_gbool_par(
        true,
        Vec::new(),
        false
    )));
    assert!(!mettail_rholang_runtime::is_binder_closed(&new_wildcard_par(Vec::new(), true)));
    // An UNKNOWN `Par` shape (no exprs, no processes) is the empty `Par`: vacuously closed but
    // not a decidable guard, so it can never discharge.
    assert!(mettail_rholang_runtime::is_binder_closed(&Par::default()));
    assert_eq!(machine_verdict(&Par::default()), None);
}
