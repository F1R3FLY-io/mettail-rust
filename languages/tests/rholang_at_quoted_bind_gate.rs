//! End-to-end reading counts for the `@` quoted-bind gate (test T-A6).
//!
//! `formal/rocq/prattail_wpda_runtime/theories/AtQuotedBindGate.v` models the
//! evidence gate `prefix_at_quoted_bind_gate_evidence` at the InputBind `@`
//! dispatch. Part B proves that the running code keeps two readings of a quoted
//! bind pattern (`current_g2a_two_readings`). Part C proves that the corrected
//! gate keeps exactly the quoted reading (`gate_single_valued`) and loses no
//! legitimate reading (`gate_no_loss`, `fixed_keeps_polyadic`). The rows below
//! bind those theorems to the generated parser: each row counts the forest of
//! the ambiguity-preserving entry `Proc::parse_via_wpda_all`.
//!
//! The same gate also guards the two Proc buckets `(` and `@`
//! (`prefix_arm_c0_a1`, `prefix_arm_c0_a3`). The Proc rows pin their reading
//! counts, so that a change to the gate that loses a Proc reading fails here.
//!
//! A row expects `Some(n)` for a forest of `n` readings, or `None` for a parse
//! error. A failing check prints every row with its readings.

use mettail_languages::rholang::{InputBind, Proc};
use proptest::prelude::*;

fn forest(source: &str) -> Result<Vec<String>, String> {
    mettail_runtime::clear_var_cache();
    let parsed = Proc::parse_via_wpda_all(source);
    mettail_runtime::clear_var_cache();
    parsed
        .map(|readings| {
            readings
                .iter()
                .map(|reading| format!("{reading:?}"))
                .collect()
        })
        .map_err(|err| format!("{err:?}"))
}

fn check_rows(rows: &[(&str, Option<usize>)]) {
    let mut report = String::new();
    let mut mismatches = 0usize;
    for (source, expected) in rows {
        let observed = forest(source);
        let observed_count = observed.as_ref().ok().map(Vec::len);
        if observed_count != *expected {
            mismatches += 1;
        }
        report
            .push_str(&format!("{source:?}: expected {expected:?}, observed {observed_count:?}\n"));
        match &observed {
            Ok(readings) => {
                for (index, reading) in readings.iter().enumerate() {
                    report.push_str(&format!("    [{index}] {reading}\n"));
                }
            },
            Err(err) => report.push_str(&format!("    error: {err}\n")),
        }
    }
    println!("{report}");
    assert_eq!(mismatches, 0, "{mismatches} row(s) differ:\n{report}");
}

/// Rocq: `AtQuotedBindGate.gate_single_valued`. A quoted bind pattern followed
/// by a bind trigger (`<-` or `<=`) has exactly the quoted reading.
#[test]
fn a_quoted_bind_pattern_has_exactly_the_quoted_reading() {
    check_rows(&[
        (r#"for(@x <- @"c"){Nil}"#, Some(1)),
        (r#"for(@x <= @"c"){Nil}"#, Some(1)),
        (r#"for(@x <- @"c"!?(1)){Nil}"#, Some(1)),
        (r#"for(@{for(@y <- d){Nil}} <- c){Nil}"#, Some(1)),
        (r#"for(@x <- @"c" where x > 0) { @"OUT"!(x) }"#, Some(1)),
    ]);
}

/// Rocq: `AtQuotedBindGate.fixed_keeps_polyadic` and
/// `AtQuotedBindGate.s1_edit1_loses_polyadic_parse`. A comma before the bind
/// trigger keeps the polyadic parse.
#[test]
fn a_polyadic_quoted_bind_keeps_its_parse() {
    check_rows(&[
        (r#"for(@x, @y <- c){Nil}"#, Some(1)),
        (r#"for(@{for(a <- b ; c <- d ; e <- f){Nil}} , @z <- g){Nil}"#, Some(1)),
    ]);
}

/// The Proc `@` and `(` buckets keep every reading.
#[test]
fn the_gated_proc_buckets_keep_their_readings() {
    check_rows(&[
        (r#"@x!(1)"#, Some(2)),
        (r#"@x!!(1)"#, Some(1)),
        (r#"@x!()"#, Some(3)),
        (r#"@x!(1, 2)"#, Some(2)),
        (r#"@Nil!(1)"#, Some(1)),
        (r#"@{for(x <- y){Nil}}!(1)"#, Some(1)),
        (r#"@Set(1)!(2)"#, Some(1)),
        (r#"@x :: ()"#, Some(1)),
        (r#"@x!(1) :: ()"#, Some(1)),
        (r#"(@x!(1)) :: ()"#, Some(3)),
        (r#"(x!(1))"#, Some(1)),
        (r#"(x)!(1)"#, Some(2)),
    ]);
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(128))]

    #[test]
    fn generated_bind_gate_keeps_the_declared_pattern_family(depth in 0usize..4, mode in 0u8..8, suffix in 0u16..1000) {
        mettail_runtime::clear_var_cache();
        let mut pattern = format!("x{suffix}");
        for _ in 0..depth {
            pattern = format!("{{for(a <- b ; c <- d ; e <- f){{{pattern}}}}}");
        }
        let source = match mode {
            0 => format!("@{pattern} <- channel"),
            1 => format!("@{pattern} <= channel"),
            2 => format!("@{pattern} <- channel!?(1)"),
            3 => format!("@{pattern}, @z <- channel"),
            4 => format!("@{pattern}, @z <= channel"),
            5 => format!("x{suffix} <- channel"),
            6 => format!("x{suffix} <= channel"),
            _ => format!("x{suffix} <- channel!?(1)"),
        };
        let readings = InputBind::parse_via_wpda_all(&source).unwrap();
        prop_assert_eq!(readings.len(), 1, "{}: {:?}", source, readings);
        prop_assert!(matches!((&readings[0], mode),
            (InputBind::InputBindQuoted(..), 0)
            | (InputBind::InputBindQuotedPersistent(..), 1)
            | (InputBind::InputBindQuotedQuery(..), 2)
            | (InputBind::InputBindPolyadic(..), 3)
            | (InputBind::InputBindPersistentPolyadic(..), 4)
            | (InputBind::InputBind(..), 5)
            | (InputBind::InputBindPersistent(..), 6)
            | (InputBind::InputBindQuery(..), 7)
        ));
        let monolithic = InputBind::__all_with_weights_monolithic(&source).unwrap();
        prop_assert_eq!(&readings, &monolithic.0);
        let elected = InputBind::parse_via_wpda(&source).unwrap();
        prop_assert_eq!(&readings[0], &elected);
        mettail_runtime::clear_var_cache();
    }

    #[test]
    fn send_triggers_do_not_suppress_cost_signature_sources(value in 0u16..1000) {
        mettail_runtime::clear_var_cache();
        let source = format!("@channel!({value}) :: ()");
        let readings = Proc::parse_via_wpda_all(&source).unwrap();
        prop_assert_eq!(readings.len(), 1);
        prop_assert!(matches!(&readings[0], Proc::PCostStackCons(..)));
        mettail_runtime::clear_var_cache();
    }
}

#[test]
fn ungrouped_postfix_quote_operands_violate_the_declared_prefix_floor() {
    for source in ["(@@Nil!().A())!(Nil)", "(@@Nil!!()[*])!()"] {
        assert!(Proc::__all_with_weights_monolithic(source).is_err(), "{source}");
        assert!(Proc::parse_via_wpda_all_with_weights(source).is_err(), "{source}");
        assert!(Proc::parse(source).is_err(), "{source}");
    }
}

#[test]
fn grouped_postfix_quote_operand_keeps_the_enclosing_send() {
    for source in ["(@(@Nil!().A()))!(Nil)", "(@(@Nil!!()[*]))!()"] {
        let (readings, _) = Proc::__all_with_weights_monolithic(source)
            .unwrap_or_else(|error| panic!("main parser rejected {source:?}: {error}"));
        assert!(!readings.is_empty());
        let value = Proc::parse(source)
            .unwrap_or_else(|error| panic!("facade rejected {source:?}: {error}"));
        assert!(readings.contains(&value), "facade reading must occur in the main forest");
        match (&value, source.ends_with("!(Nil)")) {
            (Proc::POutput(_, payload), true) => assert_eq!(payload.as_ref(), &Proc::PZero),
            (Proc::POutputEmpty(_), false) => {},
            _ => panic!("the complete enclosing send must remain: {value:?}"),
        }
        let canonical = value.to_string();
        let reparsed = Proc::parse(&canonical)
            .unwrap_or_else(|error| panic!("canonical {canonical:?} failed: {error}"));
        assert_eq!(reparsed.to_string(), canonical);
    }
}
