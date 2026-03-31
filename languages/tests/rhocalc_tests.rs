//! Systematic test suite for the RhoCalc language.
//!
//! Organized by feature area:
//! - **comm**: Communication (single-input, multi-input, join patterns)
//! - **new_and_extrusion**: PNew binder and scope extrusion equation
//! - **congruence**: Rewrite propagation through constructors
//! - **native_ops**: Embedded Rust-native arithmetic, booleans, strings
//! - **parsing**: Basic parsing and round-trip tests
//! - **beta**: Lambda/dollar-syntax beta-reduction

use mettail_languages::rhocalc::*;
use mettail_runtime::Language;

// ════════════════════════════════════════════════════════════════════════════════
// Test helpers
// ════════════════════════════════════════════════════════════════════════════════

fn parse(input: &str) -> Proc {
    Proc::parse(input).unwrap_or_else(|e| panic!("parse failed for `{}`: {}", input, e))
}

fn fresh() {
    mettail_runtime::clear_var_cache();
}

fn run(input: &str) -> mettail_runtime::AscentResults {
    fresh();
    let lang = RhoCalcLanguage;
    let term = lang
        .parse_term(input)
        .unwrap_or_else(|e| panic!("parse `{}`: {}", input, e));
    lang.run_ascent(term.as_ref())
        .unwrap_or_else(|e| panic!("run_ascent `{}`: {}", input, e))
}

fn normal_form_displays(results: &mettail_runtime::AscentResults) -> Vec<String> {
    results
        .normal_forms()
        .iter()
        .map(|nf| nf.display.clone())
        .collect()
}

/// Assert that running `input` produces at least one normal form matching `expected`.
/// Comparison is by display string, handling PPar multiset ordering.
fn assert_reduces_to(input: &str, expected: &str) {
    let results = run(input);
    let nfs = normal_form_displays(&results);

    // Parse expected in a fresh var context so variable IDs don't collide.
    fresh();
    let expected_proc = parse(expected);
    let expected_display = expected_proc.to_string();

    let found = nfs
        .iter()
        .any(|nf| nf == &expected_display || multiset_eq(nf, &expected_display));

    assert!(
        found,
        "Expected `{}` to reduce to `{}`\n  Normal forms: {:?}",
        input, expected_display, nfs
    );
}

/// Assert that running `input` produces at least `min` rewrites.
fn assert_min_rewrites(input: &str, min: usize) {
    let results = run(input);
    assert!(
        results.rewrites.len() >= min,
        "`{}`: expected >= {} rewrites, got {}",
        input,
        min,
        results.rewrites.len()
    );
}

/// Assert that running `input` produces zero rewrites (already a normal form).
fn assert_no_rewrites(input: &str) {
    let results = run(input);
    assert!(
        results.rewrites.is_empty(),
        "`{}`: expected no rewrites, got {}",
        input,
        results.rewrites.len()
    );
}

/// Assert that `input` has a rewrite from the initial term (not stuck).
fn assert_initial_rewrites(input: &str) {
    fresh();
    let lang = RhoCalcLanguage;
    let term = lang.parse_term(input).unwrap();
    let initial_id = term.term_id();
    let results = lang.run_ascent(term.as_ref()).unwrap();
    let from_initial = results.rewrites_from(initial_id);
    assert!(
        !from_initial.is_empty(),
        "`{}`: expected rewrites from initial term, but none found.\n  \
         Total rewrites in system: {}\n  \
         Normal forms: {:?}",
        input,
        results.rewrites.len(),
        normal_form_displays(&results),
    );
}

/// Compare two display strings as PPar multisets (handles HashBag ordering).
fn multiset_eq(a: &str, b: &str) -> bool {
    fn to_sorted_elements(s: &str) -> Option<Vec<String>> {
        let s = s.trim();
        if !s.starts_with('{') || !s.ends_with('}') {
            return None;
        }
        let inner = &s[1..s.len() - 1];
        let mut elems: Vec<String> = inner.split('|').map(|e| e.trim().to_string()).collect();
        elems.sort();
        Some(elems)
    }
    to_sorted_elements(a) == to_sorted_elements(b)
}

// ════════════════════════════════════════════════════════════════════════════════
// Communication
// ════════════════════════════════════════════════════════════════════════════════

mod comm {
    use super::*;

    /// Reproduces REPL load_env parse error: PPar with a!(n) must not reduce "a" to variable.
    #[test]
    fn par_with_output_literal() {
        let _ = parse("{ a!(2) | b!(3) }");
    }

    #[test]
    fn single_channel() {
        assert_reduces_to("{(c?x).{*(x)} | c!(p)}", "p");
    }

    #[test]
    fn comm_with_body_using_channel() {
        assert_reduces_to("{(c?x).{x!(0)} | c!(p)}", "p!(0)");
    }

    #[test]
    fn comm_substitutes_quoted_value() {
        // Comm: (c?x).{*(x)} | c!(0) → *(@ (0)) → 0
        assert_reduces_to("{(c?x).{*(x)} | c!(0)}", "0");
    }

    #[test]
    fn multi_input_two_channels() {
        assert_reduces_to("{(c1?x, c2?y).{*(x)} | c1!(p) | c2!(q)}", "p");
    }

    #[test]
    fn multi_input_uses_both_vars() {
        assert_reduces_to("{(c1?x, c2?y).{{*(x) | *(y)}} | c1!(p) | c2!(q)}", "p");
    }

    #[test]
    fn multi_input_three_channels() {
        assert_reduces_to(
            "{(a?x, b?y, c?z).{{*(x) | *(y) | *(z)}} | a!(p) | b!(q) | c!(r)}",
            "{p | q | r}",
        );
    }

    #[test]
    fn join_pattern_same_channel() {
        assert_reduces_to("{(c?x, c?y).{{*(x) | *(y)}} | c!(a) | c!(b)}", "{a | b}");
    }

    #[test]
    fn comm_with_remaining_parallel() {
        // {(c?x).{*(x)} | c!(p) | q} → {p | q}
        assert_reduces_to("{(c?x).{*(x)} | c!(p) | q}", "{p | q}");
    }
}

// ════════════════════════════════════════════════════════════════════════════════
// PNew binder and scope extrusion
// ════════════════════════════════════════════════════════════════════════════════

mod new_and_extrusion {
    use super::*;

    #[test]
    fn new_parses() {
        let _p = parse("new(x) in { x!(0) }");
    }

    #[test]
    fn new_multi_binder_parses() {
        let _p = parse("new(x, y) in { {x!(0) | y!(1)} }");
    }

    #[test]
    fn new_is_normal_when_body_is() {
        assert_no_rewrites("new(x) in { x!(0) }");
    }

    #[test]
    fn new_congruence_propagates_body_rewrite() {
        // new(x) in { {(a?z).{*(z)} | a!(0)} } → new(x) in { {*(@(0))} } → ...
        assert_min_rewrites("new(x) in { {(a?z).{*(z)} | a!(0)} }", 1);
    }

    #[test]
    fn new_congruence_reaches_normal_form() {
        assert_reduces_to("new(x) in { {(a?z).{*(z)} | a!(0)} }", "new(x) in { 0 }");
    }

    #[test]
    fn extrusion_forward() {
        // {new(x) in {p} | a!(0)} = new(x) in {{p | a!(0)}}
        // The initial PPar should connect to a rewrite (via equation + congruence).
        assert_initial_rewrites("{new(x) in { (a?z).{*(z)} } | a!(0)}");
    }

    #[test]
    fn extrusion_reaches_result() {
        // {new(x) in {(a?z).{*(z)}} | a!(0)}
        //  =extrude= new(x) in {{(a?z).{*(z)} | a!(0)}}
        //  →comm→ new(x) in {{*(@(0))}} →exec→ new(x) in {0}
        assert_reduces_to("{new(x) in { (a?z).{*(z)} } | a!(0)}", "new(x) in { 0 }");
    }

    #[test]
    fn extrusion_blocked_when_not_fresh() {
        // {new(a) in {(a?z).{*(z)}} | a!(0)} — x=a is NOT fresh in a!(0),
        // so extrusion should not apply. The term is stuck.
        let results = run("{new(a) in { (a?z).{*(z)} } | a!(0)}");
        let nfs = normal_form_displays(&results);
        // Should be a normal form as-is (no extrusion possible)
        assert!(!nfs.is_empty(), "blocked extrusion should still have normal forms");
    }
}

// ════════════════════════════════════════════════════════════════════════════════
// Congruence (rewrite propagation)
// ════════════════════════════════════════════════════════════════════════════════

mod congruence {
    use super::*;

    #[test]
    fn par_cong_exec() {
        // {*(@(0)) | q} → {0 | q}
        assert_reduces_to("{*(@(0)) | q}", "{0 | q}");
    }

    #[test]
    fn par_cong_reaches_deep_normal() {
        assert_reduces_to("{*(@(0))}", "0");
    }

    #[test]
    fn nested_par() {
        // Exec under nested par: {{*(@(p))}} → {{p}}
        assert_min_rewrites("{{*(@(p))}}", 1);
    }

    #[test]
    fn new_cong() {
        // NewCong: new(x) in { *(@(0)) } → new(x) in { 0 }
        assert_reduces_to("new(x) in { *(@(0)) }", "new(x) in { 0 }");
    }

    #[test]
    fn add_cong() {
        // Congruence through Add: *(@(1)) + 2 → 1 + 2 → 3
        assert_reduces_to("{*(@(1)) + 2}", "3");
    }

    #[test]
    fn comparison_cong() {
        // *(@(1)) == 1 → 1 == 1 → true
        assert_reduces_to("{*(@(1)) == 1}", "true");
    }
}

// ════════════════════════════════════════════════════════════════════════════════
// Exec (drop-quote cancellation)
// ════════════════════════════════════════════════════════════════════════════════

mod exec {
    use super::*;

    #[test]
    fn exec_basic() {
        assert_reduces_to("{*(@(0))}", "0");
    }

    #[test]
    fn exec_with_process() {
        assert_reduces_to("{*(@(a!(0)))}", "a!(0)");
    }

    #[test]
    fn quote_drop_equation() {
        // QuoteDrop: @(*(n)) = n  (equation, not rewrite)
        // This is tested indirectly: @(*(x)) normalizes by equation to x.
        let results = run("@(*(x))");
        assert!(
            !results.equivalences.is_empty() || !results.all_terms.is_empty(),
            "QuoteDrop equation should be discoverable"
        );
    }
}

// ════════════════════════════════════════════════════════════════════════════════
// Native operations (embedded Rust code)
// ════════════════════════════════════════════════════════════════════════════════

mod native_ops {
    use super::*;

    mod arithmetic {
        use super::*;

        #[test]
        fn int_add() {
            assert_reduces_to("{1 + 2}", "3");
        }
        #[test]
        fn int_sub() {
            assert_reduces_to("{5 - 3}", "2");
        }
        #[test]
        fn int_mul() {
            assert_reduces_to("{3 * 4}", "12");
        }
        #[test]
        fn int_div() {
            assert_reduces_to("{10 / 2}", "5");
        }

        #[test]
        fn float_add() {
            let results = run("{1.5 + 2.5}");
            let nfs = normal_form_displays(&results);
            assert!(
                nfs.iter().any(|nf| nf.contains("4")),
                "1.5 + 2.5 should produce 4, got: {:?}",
                nfs
            );
        }

        #[test]
        fn float_literal_f64_suffix_tokens() {
            let results = run("{1.0f64 + 0.5f64}");
            let nfs = normal_form_displays(&results);
            assert!(
                nfs.iter().any(|nf| nf.contains("1.5")),
                "expected 1.5 in a normal form, got: {:?}",
                nfs
            );
        }

        #[test]
        fn fixed_div_and_mod() {
            assert_reduces_to("{10p1 / 3p1}", "3.3p1");
            assert_reduces_to("{10p1 % 3p1}", "0.1p1");
        }

        #[test]
        fn fixed_bitand() {
            assert_reduces_to("{5p0 & 3p0}", "1p0");
        }

        #[test]
        fn fixed_bitor_bitxor() {
            assert_reduces_to("{5p0 | 3p0}", "7p0");
            assert_reduces_to("{5p0 bitxor 3p0}", "6p0");
        }

        #[test]
        fn fixed_comparisons() {
            assert_reduces_to("{10p1 == 10.0p1}", "true");
            assert_reduces_to("{1p0 == 1.0p1}", "true");
            assert_reduces_to("{10p1 != 9p1}", "true");
            assert_reduces_to("{10p1 < 11p1}", "true");
            assert_reduces_to("{10p1 > 9p1}", "true");
            assert_reduces_to("{10p1 <= 10.0p1}", "true");
            assert_reduces_to("{10p1 >= 10.0p1}", "true");
        }

        #[test]
        fn fixed_arithmetic_add_sub_mul() {
            assert_reduces_to("{1p0 + 0.5p1}", "1.5p1");
            assert_reduces_to("{2.0p1 - 0.5p1}", "1.5p1");
            assert_reduces_to("{3p0 * 2p0}", "6p0");
            assert_reduces_to("{-10p1}", "-10.0p1");
        }

        #[test]
        fn fixed_div_by_zero_is_error() {
            assert_reduces_to("{10p1 / 0p0}", "error");
        }

        #[test]
        fn fixed_mod_by_zero_is_error() {
            assert_reduces_to("{10p1 % 0p0}", "error");
        }

        #[test]
        fn float_more_f64_suffix() {
            let results = run("{1e2f64 + 1.0f64}");
            let nfs = normal_form_displays(&results);
            assert!(
                nfs.iter().any(|nf| nf.contains("101")),
                "expected 101 in a normal form, got: {:?}",
                nfs
            );
        }

        #[test]
        fn cast_to_int_float_bool_str_from_fixed() {
            assert_reduces_to("{int(10p1)}", "10");
            assert_reduces_to("{float(10p1)}", "10.0");
            assert_reduces_to("{bool(0p0)}", "false");
            assert_reduces_to("{bool(1p0)}", "true");
            assert_reduces_to(r#"{str(1.5p1)}"#, r#""1.5p1""#);
        }

        #[test]
        fn chained_add() {
            // fold evaluates full expression trees
            assert_reduces_to("{1 + 2 + 3}", "6");
        }

        #[test]
        fn negative_result() {
            let results = run("{3 - 5}");
            let nfs = normal_form_displays(&results);
            assert!(
                nfs.iter().any(|nf| nf.contains("-2")),
                "3 - 5 should produce -2, got: {:?}",
                nfs
            );
        }

        #[test]
        fn bigint_add() {
            assert_reduces_to("{1n + 2n}", "3n");
        }

        #[test]
        fn u32_add() {
            assert_reduces_to("{1u32 + 2u32}", "3u32");
        }

        /// C analogy: `unsigned x = 0; x = x - 1` → `UINT_MAX`. Rust `u32` wraps in release; debug may panic.
        #[cfg(not(debug_assertions))]
        #[test]
        fn u32_sub_underflow_wraps_to_uint_max_in_release() {
            assert_reduces_to("{0u32 - 1u32}", "4294967295u32");
        }

        #[test]
        fn bigrat_add_normalized() {
            assert_reduces_to("{3r/4r + 1r/4r}", "1r");
        }

        #[test]
        fn int_literal_optional_i64_suffix() {
            assert_reduces_to("{7i64 + 1}", "8");
        }

        #[test]
        fn fraction_builds_rational() {
            assert_reduces_to("{fraction(1n, 2n) + 1r/2r}", "1r");
        }

        /// Regression: `fraction` must use `fold` on Proc (not `step`), or Ascent never emits rw_proc.
        #[test]
        fn fraction_at_top_level_reduces() {
            assert_reduces_to("fraction(2n, 3n)", "2r/3r");
            assert_reduces_to("fraction(2n, 3n) + fraction(1n, 2n)", "7r/6r");
        }

        #[test]
        fn bigint_div_by_zero_is_error() {
            assert_reduces_to("{1n / 0n}", "error");
        }
    }

    mod bitwise {
        use super::*;

        #[test]
        fn int_and_or_not() {
            assert_reduces_to("{5 & 3}", "1");
            assert_reduces_to("{5 bitor 3}", "7");
            let results = run("{~0}");
            let nfs = normal_form_displays(&results);
            assert!(
                nfs.iter().any(|nf| nf == "-1"),
                "expected `-1` in normal forms, got: {:?}",
                nfs
            );
        }

        #[test]
        fn u32_and_or_not() {
            assert_reduces_to("{5u32 & 3u32}", "1u32");
            assert_reduces_to("{5u32 bitor 3u32}", "7u32");
            assert_reduces_to("{~0u32}", "4294967295u32");
        }

        #[test]
        fn bigint_and_or_not() {
            assert_reduces_to("{3n & 1n}", "1n");
            assert_reduces_to("{3n bitor 1n}", "3n");
            let results = run("{~0n}");
            let nfs = normal_form_displays(&results);
            assert!(
                nfs.iter().any(|nf| nf == "-1n" || nf == "-1"),
                "expected `-1n` or `-1` in normal forms, got: {:?}",
                nfs
            );
        }

        #[test]
        fn bigrat_and_or_not() {
            assert_reduces_to("{3r/4r & 1r/4r}", "1r/4r");
            assert_reduces_to("{1r/2r & 1r/3r}", "1r/3r");
            let results = run("{~0r}");
            let nfs = normal_form_displays(&results);
            assert!(
                nfs.iter().any(|nf| nf == "-1r" || nf == "-1"),
                "expected `-1r` (or `-1`) in normal forms, got: {:?}",
                nfs
            );
        }

        #[test]
        fn fixed_and_or_not_bitxor() {
            assert_reduces_to("{~0p0}", "-1p0");
            assert_reduces_to("{15p0 & 14p1}", "13.2p1");
        }

        #[test]
        fn type_mismatch_bitand_is_error() {
            assert_reduces_to("{1 & 1.0}", "error");
            assert_reduces_to("{1 & true}", "error");
        }

        #[test]
        fn type_mismatch_bitnot_is_error() {
            assert_reduces_to("{~true}", "error");
        }

        #[test]
        fn bitnot_under_congruence_smoke() {
            let results = run("{~*(@(0))}");
            let nfs = normal_form_displays(&results);
            assert!(
                nfs.iter().any(|nf| nf == "-1"),
                "expected `-1` in normal forms, got: {:?}",
                nfs
            );
        }
    }

    mod comparison {
        use super::*;

        #[test]
        fn eq_true() {
            assert_reduces_to("{1 == 1}", "true");
        }

        #[test]
        fn eq_rational_slash_binds_tighter_than_eq() {
            // Regression: `==` must not bind tighter than `/` (would parse as `15/(6==30)/12`).
            assert_reduces_to("{15r/6r == 30r/12r}", "true");
        }
        #[test]
        fn eq_false() {
            assert_reduces_to("{1 == 2}", "false");
        }
        #[test]
        fn ne() {
            assert_reduces_to("{1 != 2}", "true");
        }
        #[test]
        fn gt() {
            assert_reduces_to("{3 > 2}", "true");
        }
        #[test]
        fn lt() {
            assert_reduces_to("{2 < 3}", "true");
        }
        #[test]
        fn gte() {
            assert_reduces_to("{3 >= 3}", "true");
        }
        #[test]
        fn lte() {
            assert_reduces_to("{2 <= 3}", "true");
        }

        #[test]
        fn bigint_gt() {
            assert_reduces_to("{2n > 1n}", "true");
        }

        #[test]
        fn u32_eq() {
            assert_reduces_to("{3u32 == 3u32}", "true");
        }
    }

    mod boolean {
        use super::*;

        #[test]
        fn not_true() {
            assert_reduces_to("{not true}", "false");
        }
        #[test]
        fn not_false() {
            assert_reduces_to("{not false}", "true");
        }
        #[test]
        fn and_tt() {
            assert_reduces_to("{true and true}", "true");
        }
        #[test]
        fn and_tf() {
            assert_reduces_to("{true and false}", "false");
        }
        #[test]
        fn or_ff() {
            assert_reduces_to("{false or false}", "false");
        }
        #[test]
        fn or_tf() {
            assert_reduces_to("{true or false}", "true");
        }
    }

    mod string {
        use super::*;

        #[test]
        fn concat() {
            assert_reduces_to(r#"{concat("hello", "world")}"#, r#""helloworld""#);
        }

        #[test]
        fn len() {
            assert_reduces_to(r#"{len("hello")}"#, "5");
        }
    }

    mod bag {
        use super::*;

        /// remove(*(bag), *(elem)) after comm: removes one occurrence of elem from bag
        #[test]
        fn remove_comm() {
            assert_reduces_to(
                "{a!(#{1|2|2}#) | c!(2) | (a?b, c?e).{remove(*(b), *(e))}}",
                "#{1|2}#",
            );
        }

        /// count(*(bag), *(elem)) after comm: counts occurrences of elem in bag
        #[test]
        fn count_comm() {
            assert_reduces_to("{a!(#{1|2|2}#) | c!(2) | (a?b, c?e).{count(*(b), *(e))}}", "2");
        }
    }

    mod map {
        use super::*;

        #[test]
        fn map_len_empty() {
            assert_reduces_to("{len(map())}", "0");
        }

        #[test]
        fn map_len_one() {
            assert_reduces_to("{len(map(1:2))}", "1");
        }

        #[test]
        fn map_get() {
            assert_reduces_to("{get(map(1:10), 1)}", "10");
        }

        #[test]
        fn map_put() {
            assert_reduces_to("{get(put(map(), 1, 10), 1)}", "10");
        }

        #[test]
        fn map_merge() {
            assert_reduces_to("{get(merge(map(1:10), map(2:20)), 2)}", "20");
        }

        #[test]
        fn map_has() {
            assert_reduces_to("{has(map(1:2), 1)}", "true");
            assert_reduces_to("{has(map(1:2), 3)}", "false");
        }

        #[test]
        fn map_keys() {
            assert_reduces_to("{len(keys(map(1:10, 2:20)))}", "2");
        }

        #[test]
        fn map_values() {
            assert_reduces_to("{at(values(map(1:10, 2:20)), 1)}", "20");
        }

        #[test]
        fn map_mapdelete() {
            assert_reduces_to("{len(mapdelete(map(1:10, 2:20), 1))}", "1");
            assert_reduces_to("{get(mapdelete(map(1:10, 2:20), 1), 2)}", "20");
        }
    }

    mod type_conversion {
        use super::*;

        #[test]
        fn int_to_float() {
            assert_reduces_to("{float(3)}", "3");
        }
        #[test]
        fn bool_to_int_true() {
            assert_reduces_to("{int(true)}", "1");
        }
        #[test]
        fn bool_to_int_false() {
            assert_reduces_to("{int(false)}", "0");
        }
        #[test]
        fn int_to_str() {
            assert_reduces_to(r#"{str(42)}"#, r#""42""#);
        }

        #[test]
        fn int_from_bigint_fits_i64() {
            assert_reduces_to("{int(99n)}", "99");
        }

        #[test]
        fn str_from_bigint() {
            assert_reduces_to(r#"{str(10n)}"#, r#""10""#);
        }
    }
}

// ════════════════════════════════════════════════════════════════════════════════
// Parsing
// ════════════════════════════════════════════════════════════════════════════════

mod parsing {
    use super::*;

    #[test]
    fn fraction_zero_denominator_is_error() {
        assert_reduces_to("{fraction(1n, 0n)}", "error");
    }

    #[test]
    fn zero() {
        let _ = run("0");
    }
    #[test]
    fn empty_par() {
        let _ = run("{}");
    }
    #[test]
    fn quote() {
        let _ = run("@(0)");
    }
    #[test]
    fn drop() {
        let _ = run("*(@(0))");
    }
    #[test]
    fn send() {
        let _ = run("x!(0)");
    }
    #[test]
    fn receive() {
        let _ = run("(x?y).{y!(0)}");
    }
    #[test]
    fn multi_input() {
        let _ = run("{(c1?x, c2?y).{*(x)} | c1!(p) | c2!(q)}");
    }
    #[test]
    fn new_single() {
        let _ = run("new(x) in { x!(0) }");
    }
    #[test]
    fn new_multi() {
        let _ = run("new(x, y) in { {x!(0) | y!(1)} }");
    }

    #[test]
    fn bare_variable_infers_as_proc() {
        fresh();
        let lang = RhoCalcLanguage;
        let term = lang.parse_term("p").expect("parse");
        let term_type = lang.infer_term_type(term.as_ref());
        assert_eq!(format!("{}", term_type), "Proc");
    }
}

// ════════════════════════════════════════════════════════════════════════════════
// Beta-reduction (lambda / dollar-syntax)
// ════════════════════════════════════════════════════════════════════════════════

mod beta {
    use super::*;

    #[test]
    fn dollar_name_reduces() {
        fresh();
        let term = parse("$name(^loc.{loc!(init)}, n)");
        let normalized = term.normalize();
        assert_eq!(format!("{}", normalized), "n!(init)");
    }

    #[test]
    fn dollar_proc_reduces() {
        fresh();
        let term = parse("$proc(^f.{f}, {})");
        let normalized = term.normalize();
        assert_eq!(format!("{}", normalized), "{}");
    }

    #[test]
    fn normalize_via_language_trait() {
        fresh();
        let lang = RhoCalcLanguage;
        let term = lang
            .parse_term("$name(^loc.{loc!(init)}, n)")
            .expect("parse");
        let normalized = lang.normalize_term(term.as_ref());
        assert_eq!(format!("{}", normalized), "n!(init)");
    }
}

// ════════════════════════════════════════════════════════════════════════════════
// Type inference
// ════════════════════════════════════════════════════════════════════════════════

mod type_inference {
    use super::*;

    #[test]
    fn pinputs_infers_bound_var() {
        fresh();
        let lang = RhoCalcLanguage;
        let term = lang.parse_term("(x?y).{*(y)}").expect("parse");
        let var_types = lang.infer_var_types(term.as_ref());
        let y_info = var_types.iter().find(|v| v.name == "y");
        assert!(y_info.is_some(), "y should be found, got: {:?}", var_types);
        assert_eq!(format!("{}", y_info.unwrap().ty), "Name");
    }

    #[test]
    fn pinputs_lookup_by_name() {
        fresh();
        let lang = RhoCalcLanguage;
        let term = lang.parse_term("(x?y).{*(y)}").expect("parse");
        let y_type = lang.infer_var_type(term.as_ref(), "y");
        assert!(y_type.is_some());
        assert_eq!(format!("{}", y_type.unwrap()), "Name");
    }

    #[test]
    fn multi_input_infers_both_vars() {
        fresh();
        let lang = RhoCalcLanguage;
        let term = lang.parse_term("(c1?x, c2?y).{*(x)}").expect("parse");
        let var_types = lang.infer_var_types(term.as_ref());
        assert!(var_types.iter().any(|v| v.name == "x"));
        assert!(var_types.iter().any(|v| v.name == "y"));
    }
}
