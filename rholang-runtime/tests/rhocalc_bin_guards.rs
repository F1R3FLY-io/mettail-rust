//! CI gate for the `rhocalc` binary's PARSE ENTRY.
//!
//! `rholang-runtime/tests/rhocalc_guard_lowering.rs` pins the guard/arity semantics through the
//! library (`parse_via_wpda` + `lower_rhocalc_proc`). This file pins the one thing that suite
//! structurally cannot: that the BINARY reaches that lowering with the term the user wrote.
//!
//! The binary used to call `Proc::parse`, which is `parse_structured`: it starts from
//! `parse_via_wpda(input)` — the correct term — and then, whenever `display(parsed) != input`,
//! replaces the returned representative with the reparse of its own DISPLAY, accepting it as soon
//! as the display reaches a fixpoint. Display stability is not term preservation. RhoCalc's
//! display renders a projection operand of an arithmetic / relational / boolean operator through
//! a PROJECTION SURFACE (`macros/src/gen/syntax/display.rs::find_projection_surface_wrapper`),
//! which elects `POutputNil . q:Proc |- "@" "Nil" "!" "(" q ")"`, so
//!
//! ```text
//!   parse_via_wpda("1 + 2") = Add(CastInt 1, CastInt 2)        ← correct
//!   display(that)           = "@Nil!(1) + @Nil!(2)"            ← NOT term-preserving
//!   Proc::parse("1 + 2")    = Add(POutputNil 1, POutputNil 2)  ← two SENDS, not two numbers
//! ```
//!
//! and every `where` guard containing a literal in operator position silently stopped firing.
//!
//! These tests therefore run the REAL binary end-to-end. A library-level test cannot catch a
//! regression of the parse entry, because it never goes through it.
#![cfg(all(feature = "rhocalc-runtime", feature = "lambda-runtime"))]

use std::path::PathBuf;
use std::process::Command;

/// The distinctive firing marker — see `rhocalc_guard_lowering.rs`'s teeth-test rationale. It is
/// never a substring of a guard, a datum, or an un-fired residual.
const FIRED_MARKER: &str = "ZQFIREDZQ";

/// Write `program` to a uniquely named file under the target tmpdir and run the binary on it.
fn run(name: &str, program: &str) -> String {
    let mut path = PathBuf::from(env!("CARGO_TARGET_TMPDIR"));
    path.push(format!("rhocalc_bin_guards_{name}.rho"));
    std::fs::write(&path, program).expect("the probe program must be writable");

    let output = Command::new(env!("CARGO_BIN_EXE_rhocalc"))
        .arg(&path)
        .env("RUST_MIN_STACK", "8388608")
        .output()
        .expect("the rhocalc binary must run");
    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    assert!(
        output.status.success(),
        "rhocalc exited non-zero on {program}\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    stdout
}

/// Did the guarded body fire? The marker only ever reaches stdout as an `@"OUT"` OBSERVATION —
/// the binary never echoes the residual program — so this cannot be satisfied by an un-fired
/// receive whose body merely mentions the marker.
fn fired(name: &str, program: &str) -> bool {
    run(name, program).contains(FIRED_MARKER)
}

fn guarded(guard: &str, datum: &str) -> String {
    format!(
        r#"{{ for(@x <- @"c" where {guard}) {{ @"OUT"!("{FIRED_MARKER}") }} | @"c"!({datum}) }}"#
    )
}

/// The teeth test, at the binary level: the detector must separate a known firing from a known
/// non-firing before any assertion below is trusted.
#[test]
fn binary_harness_has_teeth() {
    assert!(
        fired("teeth_true", &guarded("true", "42")),
        "the binary harness cannot observe a firing: `where true` must publish the marker"
    );
    assert!(
        !fired("teeth_false", &guarded("false", "42")),
        "the binary harness reports a firing that did not happen"
    );
}

/// The headline regression: a guard comparing a BOUND variable against a literal. Under
/// `Proc::parse` the literal lowered to a `Send` and the structural `EEq` answered `false`,
/// silently — no error, no COMM, nothing to see.
#[test]
fn binary_fires_a_guard_comparing_a_bound_variable_to_a_literal() {
    assert!(
        fired("eq_literal", &guarded("x == 42", "42")),
        "`where x == 42` with datum 42 must fire through the binary"
    );
    assert!(
        !fired("eq_literal_false", &guarded("x == 99", "42")),
        "`where x == 99` with datum 42 must NOT fire through the binary"
    );
}

/// The asymmetry that identified the root: under the defect `!=` fired while `==` did not,
/// because both were decided by a STRUCTURAL comparison against a `Send`. Pinning both directions
/// makes that failure mode unreachable without a test going red.
#[test]
fn binary_agrees_on_equality_and_disequality() {
    assert!(fired("ne_true", &guarded("x != 43", "42")), "`x != 43` with 42 is TRUE");
    assert!(!fired("ne_false", &guarded("x != 42", "42")), "`x != 42` with 42 is FALSE");
    assert!(fired("eq_true", &guarded("x == 42", "42")), "`x == 42` with 42 is TRUE");
    assert!(!fired("eq_false", &guarded("x == 43", "42")), "`x == 43` with 42 is FALSE");
}

/// Relational, arithmetic and boolean guards through the binary — the three families that raised
/// a hard `ReduceError` in send position and failed silently in guard position.
#[test]
fn binary_fires_relational_arithmetic_and_boolean_guards() {
    for (name, guard, datum) in [
        ("lt_bound", "x < 46", "42"),
        ("gt_bound", "x > 0", "7"),
        ("gte_bound", "x >= 42", "42"),
        ("arith_bound", "x + 1 > 0", "7"),
        ("lt_ground", "1 < 46", "42"),
        ("and_ground", "true and true", "42"),
        ("or_bound", "x or false", "true"),
        ("not_ground", "not false", "42"),
        ("matches_bound", "x matches 42", "42"),
    ] {
        assert!(
            fired(name, &guarded(guard, datum)),
            "`where {guard}` with datum {datum} is TRUE and must fire through the binary"
        );
    }
}

/// The send-position diagnostics: the same operands that broke guards silently broke sends
/// LOUDLY. These pin the loud half, which is what makes a future regression findable.
#[test]
fn binary_evaluates_operators_in_send_position() {
    // ★ These were `Int(3)` / `Bool(true)` — `RuntimeObservationValue`'s Rust `Debug` spelling,
    // which the interpreter used to print because `render_obs`'s fallback arm was
    // `format!("{other:?}")`. That fallback is why a `^spec-failure` datum printed as a
    // re-quoted prost dump, and removing it routed every non-`Term` observation through
    // `Display` instead. So the binary now prints the VALUE — `⟦3⟧`, `⟦true⟧` — and these
    // expectations are updated to the value rather than to the debug spelling of its carrier.
    //
    // The `⟦…⟧` delimiters are kept in the needle deliberately: a bare `"3"` would match any
    // stdout containing a 3, including the source echo, and this cell exists to pin the
    // observation.
    for (name, payload, expected) in [
        ("send_plus", "1 + 2", "⟦3⟧"),
        ("send_minus", "7 - 2", "⟦5⟧"),
        ("send_lt", "1 < 46", "⟦true⟧"),
        ("send_and", "true and true", "⟦true⟧"),
        ("send_not", "not false", "⟦true⟧"),
        ("send_or", "false or true", "⟦true⟧"),
    ] {
        let stdout = run(name, &format!(r#"{{ @"OUT"!({payload}) }}"#));
        assert!(
            stdout.contains(expected),
            "`@\"OUT\"!({payload})` must observe {expected} through the binary\nstdout:\n{stdout}"
        );
    }
}

/// The monadic receive arity, through the binary: a scalar ground pattern matches a scalar send
/// and NOT a one-element-list send. Before the fix this held exactly backwards.
#[test]
fn binary_matches_a_scalar_ground_pattern_against_a_scalar_send() {
    let scalar = format!(r#"{{ for(@42 <- @"c") {{ @"OUT"!("{FIRED_MARKER}") }} | @"c"!(42) }}"#);
    assert!(fired("arity_scalar", &scalar), "`for(@42 <- c)` must match `c!(42)`");

    let listed = format!(r#"{{ for(@42 <- @"c") {{ @"OUT"!("{FIRED_MARKER}") }} | @"c"!([42]) }}"#);
    assert!(!fired("arity_listed", &listed), "`for(@42 <- c)` must NOT match `c!([42])`");
}
