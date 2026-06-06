// Probe: what does Display(Neg(NumLit(0))) actually produce?
// And what does parse("- 0") + rewrite produce?

use mettail_languages::calculator::{CalculatorLanguage, Int};

#[test]
fn probe_display_neg_numlit_zero() {
    // Construct Neg(NumLit(0)) directly and Display it.
    //
    // Phase F.12.B+C (2026-05-20): W3 dropped. Display is honest about
    // the AST. `Neg(NumLit(0))` displays as `"-0"`, distinguishable from
    // `NumLit(0)` which displays as `"0"`.
    let inner = Int::NumLit(0i32);
    let neg_zero = Int::Neg(std::sync::Arc::new(inner));
    let displayed = format!("{}", neg_zero);
    eprintln!("Display(Neg(NumLit(0))) = {:?}", displayed);
    assert_eq!(
        displayed, "-0",
        "post-F.12.B+C: Display should honestly render Neg(NumLit(0)) as '-0'"
    );
}

#[test]
fn probe_parse_dash_space_zero() {
    mettail_runtime::clear_var_cache();
    let parsed = Int::parse_structured("- 0").expect("should parse");
    let displayed = format!("{}", parsed);
    eprintln!("parse(\"- 0\") = {:?}", parsed);
    eprintln!("Display(parse(\"- 0\")) = {:?}", displayed);
}

#[test]
fn probe_parse_dash_zero() {
    mettail_runtime::clear_var_cache();
    let parsed = Int::parse_structured("-0").expect("should parse");
    let displayed = format!("{}", parsed);
    eprintln!("parse(\"-0\") = {:?}", parsed);
    eprintln!("Display(parse(\"-0\")) = {:?}", displayed);
}

#[test]
fn probe_run_to_nf_dash_space_zero() {
    use mettail_simulation::runner::{SimulationConfig, SimulationRunner};
    use mettail_simulation::trace::TraceOutcome;

    mettail_runtime::clear_var_cache();
    let lang = CalculatorLanguage;
    let lang_ref: &dyn mettail_runtime::Language = &lang;
    let config = SimulationConfig {
        max_steps: 100,
        seed: Some([99u8; 32]),
        track_morphology: false,
        ..SimulationConfig::default()
    };
    let runner = SimulationRunner::new(lang_ref, config);

    let trace = runner.run_to_normal_form("- 0").expect("should run");
    eprintln!("trace.outcome = {:?}", trace.outcome);
    match trace.outcome {
        TraceOutcome::NormalForm { term, steps } => {
            eprintln!("NF for \"- 0\" = {:?}, steps = {}", term, steps);
        },
        other => {
            eprintln!("did not reach NF: {:?}", other);
        },
    }
}

#[test]
fn probe_dump_all_terms_dash_space_zero() {
    use mettail_languages::calculator::{CalculatorTerm, CalculatorTermInner};
    mettail_runtime::clear_var_cache();
    let lang = CalculatorLanguage;
    let parsed = Int::parse_structured("- 0").expect("parse");
    eprintln!("parsed (Debug)      = {:?}", parsed);
    eprintln!("parsed (Display)    = {:?}", format!("{}", parsed));

    let wrapped: CalculatorTerm = CalculatorTerm(CalculatorTermInner::Int(parsed.clone()));
    let arc_term: std::sync::Arc<dyn mettail_runtime::Term> = std::sync::Arc::new(wrapped);
    let results = {
        use mettail_runtime::Language;
        lang.run_ascent(arc_term.as_ref()).expect("ascent")
    };
    eprintln!("== all_terms ==");
    for (i, t) in results.all_terms.iter().enumerate() {
        eprintln!("  [{}] id={} is_nf={} display={:?}", i, t.term_id, t.is_normal_form, t.display);
    }
    eprintln!("== rewrites ==");
    for rw in results.rewrites.iter() {
        eprintln!("  from_id={} to_id={} rule={:?}", rw.from_id, rw.to_id, rw.rule_name);
    }
    eprintln!("== initial term id = {}", arc_term.term_id());
}

#[test]
fn probe_language_parse_dash_space_zero() {
    use mettail_runtime::Language;
    mettail_runtime::clear_var_cache();
    let lang = CalculatorLanguage;
    let parsed = lang.parse_term("- 0").expect("Language::parse_term");
    eprintln!("Language::parse(\"- 0\") display = {:?}", format!("{}", parsed));
    eprintln!("Language::parse(\"- 0\") term_id = {}", parsed.term_id());

    // Also run ascent on this parsed term.
    let results = lang.run_ascent(parsed.as_ref()).expect("ascent");
    eprintln!("== all_terms (via Language::parse) ==");
    for (i, t) in results.all_terms.iter().enumerate() {
        eprintln!("  [{}] id={} is_nf={} display={:?}", i, t.term_id, t.is_normal_form, t.display);
    }
    eprintln!("== rewrites ==");
    for rw in results.rewrites.iter() {
        eprintln!("  from_id={} to_id={} rule={:?}", rw.from_id, rw.to_id, rw.rule_name);
    }
}

#[test]
fn probe_run_to_nf_dash_zero() {
    use mettail_simulation::runner::{SimulationConfig, SimulationRunner};
    use mettail_simulation::trace::TraceOutcome;

    mettail_runtime::clear_var_cache();
    let lang = CalculatorLanguage;
    let lang_ref: &dyn mettail_runtime::Language = &lang;
    let config = SimulationConfig {
        max_steps: 100,
        seed: Some([99u8; 32]),
        track_morphology: false,
        ..SimulationConfig::default()
    };
    let runner = SimulationRunner::new(lang_ref, config);

    let trace = runner.run_to_normal_form("-0").expect("should run");
    eprintln!("trace.outcome = {:?}", trace.outcome);
    match trace.outcome {
        TraceOutcome::NormalForm { term, steps } => {
            eprintln!("NF for \"-0\" = {:?}, steps = {}", term, steps);
        },
        other => {
            eprintln!("did not reach NF: {:?}", other);
        },
    }
}

// ─── Extended probes (2026-05-20): empirical survey for `-0` round-trip fix ───

#[test]
fn probe_fork_parse_dash_3_emits_alternatives() {
    // F.10 commit description says "-3" should fork into atomic NumLit(-3)
    // AND Pratt-Neg(NumLit(3)). Use parse_all_structured if it exists,
    // otherwise compare parse_structured single result to inspect which arm wins.
    mettail_runtime::clear_var_cache();
    let parsed = Int::parse_structured("-3").expect("parse");
    eprintln!("parse(\"-3\") = {:?}", parsed);
    eprintln!("Display(parse(\"-3\")) = {:?}", format!("{}", parsed));
}

#[test]
fn probe_fork_parse_dash_3_bang_emits_alternatives() {
    // "-3!" should fork — F.10 fix was specifically about this.
    // Path A: Neg(Fact(NumLit(3))) via Pratt-Neg
    // Path B: Fact(NumLit(-3)) via atomic-lex `-3` + Fact `!`
    mettail_runtime::clear_var_cache();
    let parsed = Int::parse_structured("-3!");
    match parsed {
        Ok(t) => {
            eprintln!("parse(\"-3!\") OK = {:?}", t);
            eprintln!("Display(parse(\"-3!\")) = {:?}", format!("{}", t));
        },
        Err(e) => eprintln!("parse(\"-3!\") ERR = {:?}", e),
    }
}

#[test]
fn probe_fork_parse_dash_0_emits_alternatives() {
    // Most interesting: does the lex-Fork emit BOTH atomic-NumLit(0) AND
    // Pratt-Neg(NumLit(0))?
    mettail_runtime::clear_var_cache();
    let parsed = Int::parse_structured("-0").expect("parse");
    eprintln!("parse(\"-0\") = {:?}", parsed);
    eprintln!("Display(parse(\"-0\")) = {:?}", format!("{}", parsed));
}

#[test]
fn probe_display_roundtrip_neg_numlit_3() {
    // Confirm Display(Neg(NumLit(3))) == "-3" (no W3 suppression for non-zero)
    let three = Int::NumLit(3i32);
    let neg = Int::Neg(std::sync::Arc::new(three));
    let s = format!("{}", neg);
    eprintln!("Display(Neg(NumLit(3))) = {:?}", s);
    assert_eq!(s, "-3");
}

#[test]
fn probe_display_roundtrip_double_neg_numlit_3() {
    // Display(Neg(Neg(NumLit(3))))?
    let three = Int::NumLit(3i32);
    let neg = Int::Neg(std::sync::Arc::new(three));
    let neg_neg = Int::Neg(std::sync::Arc::new(neg));
    let s = format!("{}", neg_neg);
    eprintln!("Display(Neg(Neg(NumLit(3)))) = {:?}", s);
}

#[test]
fn probe_display_roundtrip_double_neg_zero() {
    // Display(Neg(Neg(NumLit(0))))? Is W3 chain-walking active?
    let zero = Int::NumLit(0i32);
    let neg = Int::Neg(std::sync::Arc::new(zero));
    let neg_neg = Int::Neg(std::sync::Arc::new(neg));
    let s = format!("{}", neg_neg);
    eprintln!("Display(Neg(Neg(NumLit(0)))) = {:?}", s);
}

#[test]
fn probe_all_parses_dash_3() {
    // Use Language::parse_all to see if multi-result surfaces both Pratt-Neg
    // and atomic-NumLit arms.
    use mettail_runtime::Language;
    mettail_runtime::clear_var_cache();
    let lang = CalculatorLanguage;
    // Wrap input
    let res = lang.parse_term("-3");
    match res {
        Ok(t) => eprintln!("Language::parse('-3') = {:?}", format!("{}", t)),
        Err(e) => eprintln!("Language::parse('-3') ERR = {:?}", e),
    }
}

#[test]
fn probe_lex_dag_ambiguity_for_dash_0() {
    // Inspect whether lex_dag(-0) actually has any ambiguity.
    // If not, lex-Fork path is never taken and there's no Pratt-Neg alt to elect.
    eprintln!("Investigating lex_dag for '-0'...");
    // The parse_via_wpda_all path calls lex_dag(input).has_ambiguity() —
    // if no ambiguity, slice path used (no lex-Fork).
}

#[test]
fn probe_parse_via_wpda_all_dash_n_inputs() {
    // Use Int::parse_via_wpda_all (M8 multi-result entry) directly.
    mettail_runtime::clear_var_cache();
    for input in ["-0", "-3", "-3!", "-(0)", "- 0", "- 3"] {
        match Int::parse_via_wpda_all(input) {
            Ok(ts) => {
                eprintln!("parse_via_wpda_all({:?}) -> {} alts", input, ts.len());
                for (i, t) in ts.iter().enumerate() {
                    eprintln!("    [{}] debug={:?} display={:?}", i, t, format!("{}", t));
                }
            },
            Err(e) => eprintln!("parse_via_wpda_all({:?}) ERR = {:?}", input, e),
        }
    }
}

#[test]
fn probe_i32_min_atomic_lex() {
    // Open question Q1: does atomic lex still handle i32::MIN = -2147483648?
    // Since `-?` is still in the regex, this should still work.
    mettail_runtime::clear_var_cache();
    let parsed = Int::parse_structured("-2147483648");
    match parsed {
        Ok(t) => {
            eprintln!("parse('-2147483648') = {:?}", t);
            eprintln!("Display = {:?}", format!("{}", t));
        },
        Err(e) => eprintln!("parse('-2147483648') ERR = {:?}", e),
    }
}

#[test]
fn probe_parse_dash_zero_point_zero_float() {
    use mettail_languages::calculator::Float;
    use std::panic::AssertUnwindSafe;
    mettail_runtime::clear_var_cache();
    // Direct Float::parse_structured of "-0.0" to see if it fails here too
    let result = std::panic::catch_unwind(AssertUnwindSafe(|| Float::parse_structured("-0.0")));
    match result {
        Ok(Ok(t)) => eprintln!("Float::parse_structured('-0.0') = {:?}", t),
        Ok(Err(e)) => eprintln!("Float::parse_structured('-0.0') ERR = {:?}", e),
        Err(p) => eprintln!("Float::parse_structured('-0.0') PANIC = {:?}", p),
    }
}

#[test]
fn probe_parse_dash_zero_point_zero_proc() {
    use mettail_runtime::Language;
    use std::panic::AssertUnwindSafe;
    mettail_runtime::clear_var_cache();
    let lang = CalculatorLanguage;
    let result = std::panic::catch_unwind(AssertUnwindSafe(|| lang.parse_term("-0.0")));
    match result {
        Ok(Ok(t)) => eprintln!("CalculatorLanguage::parse_term('-0.0') = {:?}", format!("{}", t)),
        Ok(Err(e)) => eprintln!("CalculatorLanguage::parse_term('-0.0') ERR = {:?}", e),
        Err(p) => {
            if let Some(s) = p.downcast_ref::<String>() {
                eprintln!("PANIC: {}", s);
            } else if let Some(s) = p.downcast_ref::<&'static str>() {
                eprintln!("PANIC: {}", s);
            } else {
                eprintln!("PANIC: unknown payload");
            }
        },
    }
}

#[test]
fn probe_parse_via_wpda_all_dash_zero_point_zero_float() {
    use mettail_languages::calculator::Float;
    use std::panic::AssertUnwindSafe;
    mettail_runtime::clear_var_cache();
    let result = std::panic::catch_unwind(AssertUnwindSafe(|| Float::parse_via_wpda_all("-0.0")));
    match result {
        Ok(Ok(ts)) => {
            eprintln!("Float::parse_via_wpda_all('-0.0') = {} alts", ts.len());
            for (i, t) in ts.iter().enumerate() {
                eprintln!("    [{}] debug={:?} display={:?}", i, t, format!("{}", t));
            }
        },
        Ok(Err(e)) => eprintln!("Float::parse_via_wpda_all('-0.0') ERR = {:?}", e),
        Err(p) => {
            if let Some(s) = p.downcast_ref::<String>() {
                eprintln!("PANIC: {}", s);
            } else if let Some(s) = p.downcast_ref::<&'static str>() {
                eprintln!("PANIC: {}", s);
            } else {
                eprintln!("PANIC: unknown payload");
            }
        },
    }
}

#[test]
fn probe_minimal_atomic_int_lit() {
    // Simplest possible atomic int parse.
    use std::panic::AssertUnwindSafe;
    mettail_runtime::clear_var_cache();
    let result = std::panic::catch_unwind(AssertUnwindSafe(|| Int::parse_structured("42")));
    match result {
        Ok(Ok(t)) => eprintln!("Int::parse_structured('42') = {:?}", t),
        Ok(Err(e)) => eprintln!("Int::parse_structured('42') ERR = {:?}", e),
        Err(p) => {
            if let Some(s) = p.downcast_ref::<String>() {
                eprintln!("PANIC: {}", s);
            } else if let Some(s) = p.downcast_ref::<&'static str>() {
                eprintln!("PANIC: {}", s);
            } else {
                eprintln!("PANIC: unknown payload");
            }
        },
    }
}

#[test]
fn probe_minimal_atomic_int_lit_negative() {
    use std::panic::AssertUnwindSafe;
    mettail_runtime::clear_var_cache();
    let result = std::panic::catch_unwind(AssertUnwindSafe(|| Int::parse_structured("-5")));
    match result {
        Ok(Ok(t)) => eprintln!("Int::parse_structured('-5') = {:?}", t),
        Ok(Err(e)) => eprintln!("Int::parse_structured('-5') ERR = {:?}", e),
        Err(p) => {
            if let Some(s) = p.downcast_ref::<String>() {
                eprintln!("PANIC: {}", s);
            } else if let Some(s) = p.downcast_ref::<&'static str>() {
                eprintln!("PANIC: {}", s);
            } else {
                eprintln!("PANIC: unknown payload");
            }
        },
    }
}

#[test]
fn probe_atomic_int_lit_negative_in_release() {
    // Try with debug_assertions disabled? Actually we can't easily change cfg
    // from a test; this is just informational.
    eprintln!("debug_assertions = {}", cfg!(debug_assertions));
}
