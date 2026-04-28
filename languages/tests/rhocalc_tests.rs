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

/// Assert that a term display is never produced among discovered terms.
fn assert_never_produces(input: &str, forbidden: &str) {
    let results = run(input);
    let found = results.all_terms.iter().any(|t| t.display == forbidden);
    assert!(!found, "`{}` unexpectedly produced `{}`", input, forbidden);
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
        assert_reduces_to("{for(x <- c){*(x)} | c!(p)}", "p");
    }

    #[test]
    fn comm_with_body_using_channel() {
        assert_reduces_to("{for(x <- c){x!(0)} | c!(p)}", "p!(0)");
    }

    #[test]
    fn comm_substitutes_quoted_value() {
        // Comm: for(x <- c){*(x)} | c!(0) → *(@ (0)) → 0
        assert_reduces_to("{for(x <- c){*(x)} | c!(0)}", "0");
    }

    #[test]
    fn multi_input_two_channels() {
        assert_reduces_to("{for(x <- c1 & y <- c2){*(x)} | c1!(p) | c2!(q)}", "p");
    }

    #[test]
    fn multi_input_uses_both_vars() {
        assert_reduces_to("{for(x <- c1 & y <- c2){{*(x) | *(y)}} | c1!(p) | c2!(q)}", "p");
    }

    #[test]
    fn multi_input_three_channels() {
        assert_reduces_to(
            "{for(x <- a & y <- b & z <- c){{*(x) | *(y) | *(z)}} | a!(p) | b!(q) | c!(r)}",
            "{p | q | r}",
        );
    }

    #[test]
    fn join_pattern_same_channel() {
        assert_reduces_to("{for(x <- c & y <- c){{*(x) | *(y)}} | c!(a) | c!(b)}", "{a | b}");
    }

    #[test]
    fn comm_with_remaining_parallel() {
        // {for(x <- c){*(x)} | c!(p) | q} → {p | q}
        assert_reduces_to("{for(x <- c){*(x)} | c!(p) | q}", "{p | q}");
    }

    #[test]
    fn pattern_comm_var_matches_payload() {
        assert_reduces_to("{for(x <- c){*x} | c!(p)}", "p");
    }

    #[test]
    fn compact_for_row_with_ampersand_desugars_to_join() {
        assert_reduces_to("{for(x <- c1 & y <- c2){*x} | c1!(p) | c2!(q)}", "p");
    }

    #[test]
    fn quoted_name_binder_form_is_equivalent() {
        assert_reduces_to("{for(@x <- c1 & @y <- c2){x} | c1!(p) | c2!(q)}", "p");
    }

    #[test]
    fn compact_for_rows_with_semicolon_are_nested() {
        assert_reduces_to("{for(x <- c1; y <- c2){*x} | c1!(p) | c2!(q)}", "p");
    }

    #[test]
    fn compact_for_row_where_guard_blocks_when_false() {
        assert_never_produces("{for(x <- c1 & y <- c2 where false){*x} | c1!(p) | c2!(q)}", "{p}");
    }

    #[test]
    fn where_guard_false_is_noop_for_receive_pair() {
        assert_never_produces("{for(x <- c where false){*x} | c!(p)}", "{p}");
    }

    #[test]
    fn where_guard_expression_false_is_noop_for_receive_pair() {
        assert_never_produces("{for(x <- c where x > 3){*x} | c!(2)}", "{2}");
    }

    #[test]
    fn join_pattern_mismatch_is_noop_for_receive_group() {
        assert_reduces_to(
            "{for(@[1,2,4] <- c){7} | c!([1,2,3])}",
            "{for(@[1,2,4] <- c){7} | c!([1,2,3])}",
        );
        assert_never_produces("{for(@[1,2,4] <- c){7} | c!([1,2,3])}", "{7}");
    }

    #[test]
    fn pattern_comm_ground_pattern_matches_equal_payload() {
        assert_reduces_to("{for(@0 <- c){1} | c!(0)}", "1");
    }

    #[test]
    fn pattern_comm_exact_constructor_pattern_matches() {
        assert_reduces_to("{for(@*(@(0)) <- c){1} | c!(*(@(0)))}", "1");
    }

    #[test]
    fn pattern_comm_ground_pattern_blocks_mismatch() {
        // Pattern 0 does not match payload p, so COMM must not produce {0}.
        // (Other non-COMM rewrites may exist due HOL/native rules.)
        assert_never_produces("{for(@0 <- c){0} | c!(p)}", "{0}");
    }

    #[test]
    fn pattern_comm_list_literal_pattern_matches() {
        assert_reduces_to("{for(@[0, 1] <- c){42} | c!([0, 1])}", "42");
    }

    #[test]
    fn pattern_comm_list_literal_pattern_blocks_mismatch() {
        assert_never_produces("{for(@[0, 1] <- c){42} | c!([0, 1, 2])}", "{42}");
    }

    #[test]
    fn pattern_comm_bag_literal_pattern_matches() {
        assert_reduces_to("{for(@#{1|2}# <- c){7} | c!(#{2|1}#)}", "7");
    }

    #[test]
    fn pattern_comm_bag_literal_pattern_blocks_mismatch() {
        assert_never_produces("{for(@#{1|2}# <- c){7} | c!(#{1|1}#)}", "{7}");
    }

    #[test]
    fn pattern_comm_map_literal_pattern_matches() {
        assert_reduces_to("{for(@map(1:2, 3:4) <- c){9} | c!(map(3:4, 1:2))}", "9");
    }

    #[test]
    fn pattern_comm_map_literal_pattern_blocks_mismatch() {
        assert_never_produces("{for(@map(1:2, 3:4) <- c){9} | c!(map(1:2, 3:5))}", "{9}");
    }

    #[test]
    fn complex_join_map_and_list_literal_pattern_matches() {
        assert_reduces_to(
            "{for(@map(1:x, 3:4) <- c & @[1,2,3] <- c2 where x>1){x} | c!(map(3:4, 1:2)) | c2!([1,2,3])}",
            "2",
        );
    }

    #[test]
    fn complex_join_map_and_list_literal_pattern_blocks_mismatch() {
        assert_never_produces(
            "{for(@map(1:x, 3:4) <- c & @[1,2,4] <- c2 where x>1){x} | c!(map(3:4, 1:2)) | c2!([1,2,3])}",
            "{2}",
        );
    }

    #[test]
    fn complex_join_map_and_list_var_pattern_matches() {
        assert_reduces_to(
            "{for(@map(1:x, 3:4) <- c & @[1,2,y] <- c2 where x>1){x} | c!(map(3:4, 1:2)) | c2!([1,2,3])}",
            "2",
        );
    }

    #[test]
    fn complex_join_map_and_list_var_pattern_with_guard_matches() {
        assert_reduces_to(
            "{for(@map(1:x, 3:4) <- c & @[1,2,y] <- c2 where x>1 and y>1){x} | c!(map(3:4, 1:2)) | c2!([1,2,3])}",
            "2",
        );
    }

    #[test]
    fn complex_join_map_and_list_var_pattern_with_guard_blocks() {
        assert_never_produces(
            "{for(@map(1:x, 3:4) <- c & @[1,2,y] <- c2 where x>1 and y>3){x} | c!(map(3:4, 1:2)) | c2!([1,2,3])}",
            "{2}",
        );
    }

    #[test]
    fn complex_multi_row_join_and_followup_row_matches() {
        assert_reduces_to(
            "{for(@map(1:x, 3:4) <- c & @[1,2,y] <- c2 where x>1 and y>1; z <- c3 ){[x,z]} | c!(map(3:4, 1:2)) | c2!([1,2,3]) | c3!(11111111)}",
            "[2, 11111111]",
        );
    }

    #[test]
    fn complex_multi_row_join_and_followup_row_guard_blocks() {
        assert_never_produces(
            "{for(@map(1:x, 3:4) <- c & @[1,2,y] <- c2 where x>1 and y>1; z <- c3 where z > 1111111111111111 ){[x,z]} | c!(map(3:4, 1:2)) | c2!([1,2,3]) | c3!(11111111)}",
            "{[2, 11111111]}",
        );
    }

    #[test]
    fn join_where_guard_string_eq_matches() {
        assert_reduces_to(
            r#"{for(qty <- stock & item <- shop where (qty > 1) and (item == "lemon")){[item, qty]} | stock!(2) | shop!("lemon")}"#,
            r#"["lemon", 2]"#,
        );
    }

    #[test]
    fn join_where_guard_string_eq_blocks() {
        assert_never_produces(
            r#"{for(qty <- stock & item <- shop where (qty > 1) and (item == "lemon")){[item, qty]} | stock!(2) | shop!("lime")}"#,
            r#"["lime", 2]"#,
        );
    }

    #[test]
    fn proc_pattern_matches_list_is_strict() {
        let pat = parse("[0, 1]");
        let val = parse("[0, 1, 2]");
        assert!(!pat.pattern_matches(&val));
    }

    #[test]
    fn proc_pattern_matches_map_is_strict() {
        let pat = parse("map(1:2, 3:4)");
        let val = parse("map(1:2, 3:5)");
        assert!(!pat.pattern_matches(&val));
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
        // new(x) in { {for(z <- a){*(z)} | a!(0)} } → new(x) in { {*(@(0))} } → ...
        assert_min_rewrites("new(x) in { {for(z <- a){*(z)} | a!(0)} }", 1);
    }

    #[test]
    fn new_congruence_reaches_normal_form() {
        assert_reduces_to("new(x) in { {for(z <- a){*(z)} | a!(0)} }", "new(x) in { 0 }");
    }

    #[test]
    fn extrusion_forward() {
        // {new(x) in {p} | a!(0)} = new(x) in {{p | a!(0)}}
        // The initial PPar should connect to a rewrite (via equation + congruence).
        assert_initial_rewrites("{new(x) in { for(z <- a){*(z)} } | a!(0)}");
    }

    #[test]
    fn extrusion_reaches_result() {
        // {new(x) in {for(z <- a){*(z)}} | a!(0)}
        //  =extrude= new(x) in {{for(z <- a){*(z)} | a!(0)}}
        //  →comm→ new(x) in {{*(@(0))}} →exec→ new(x) in {0}
        assert_reduces_to("{new(x) in { for(z <- a){*(z)} } | a!(0)}", "new(x) in { 0 }");
    }

    #[test]
    fn extrusion_blocked_when_not_fresh() {
        // {new(a) in {for(z <- a){*(z)}} | a!(0)} — x=a is NOT fresh in a!(0),
        // so extrusion should not apply. The term is stuck.
        let results = run("{new(a) in { for(z <- a){*(z)} } | a!(0)}");
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
            assert_reduces_to("{5p0 bitand 3p0}", "1p0");
        }

        #[test]
        fn fixed_bitor() {
            assert_reduces_to("{5p0 bitor 3p0}", "7p0");
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
            assert_reduces_to("{int(10p1, 64)}", "10");
            assert_reduces_to("{float(10p1, 64)}", "10.0");
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
            assert_reduces_to("{5 bitand 3}", "1");
            assert_reduces_to("{5 bitor 3}", "7");
            let results = run("{bitnot 0}");
            let nfs = normal_form_displays(&results);
            assert!(
                nfs.iter().any(|nf| nf == "-1"),
                "expected `-1` in normal forms, got: {:?}",
                nfs
            );
        }

        #[test]
        fn u32_and_or_not() {
            assert_reduces_to("{5u32 bitand 3u32}", "1u32");
            assert_reduces_to("{5u32 bitor 3u32}", "7u32");
            assert_reduces_to("{bitnot 0u32}", "4294967295u32");
        }

        #[test]
        fn bigint_and_or_not() {
            assert_reduces_to("{3n bitand 1n}", "1n");
            assert_reduces_to("{3n bitor 1n}", "3n");
            let results = run("{bitnot 0n}");
            let nfs = normal_form_displays(&results);
            assert!(
                nfs.iter().any(|nf| nf == "-1n" || nf == "-1"),
                "expected `-1n` or `-1` in normal forms, got: {:?}",
                nfs
            );
        }

        #[test]
        fn bigrat_and_or_not() {
            assert_reduces_to("{3r/4r bitand 1r/4r}", "1r/4r");
            assert_reduces_to("{1r/2r bitand 1r/3r}", "1r/3r");
            let results = run("{bitnot 0r}");
            let nfs = normal_form_displays(&results);
            assert!(
                nfs.iter().any(|nf| nf == "-1r" || nf == "-1"),
                "expected `-1r` (or `-1`) in normal forms, got: {:?}",
                nfs
            );
        }

        #[test]
        fn fixed_and_or_not() {
            assert_reduces_to("{bitnot 0p0}", "-1p0");
            assert_reduces_to("{15p0 bitand 14p1}", "13.2p1");
        }

        #[test]
        fn type_mismatch_bitand_is_error() {
            assert_reduces_to("{1 bitand 1.0}", "error");
            assert_reduces_to("{1 bitand true}", "error");
        }

        #[test]
        fn type_mismatch_bitnot_is_error() {
            assert_reduces_to("{bitnot true}", "error");
        }

        #[test]
        fn bitnot_under_congruence_smoke() {
            let results = run("{bitnot *(@(0))}");
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

        #[test]
        fn str_eq() {
            assert_reduces_to(r#"{"abc" == "abc"}"#, "true");
        }

        #[test]
        fn str_ne() {
            assert_reduces_to(r#"{"abc" != "abd"}"#, "true");
        }

        #[test]
        fn str_gt_lexicographic() {
            assert_reduces_to(r#"{"b" > "a"}"#, "true");
        }

        #[test]
        fn str_lt_lexicographic() {
            assert_reduces_to(r#"{"apple" < "banana"}"#, "true");
        }

        #[test]
        fn str_gte() {
            assert_reduces_to(r#"{"abc" >= "abc"}"#, "true");
        }

        #[test]
        fn str_lte() {
            assert_reduces_to(r#"{"abc" <= "abc"}"#, "true");
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
                "{a!(#{1|2|2}#) | c!(2) | for(b <- a & e <- c){remove(*(b), *(e))}}",
                "#{1|2}#",
            );
        }

        /// count(*(bag), *(elem)) after comm: counts occurrences of elem in bag
        #[test]
        fn count_comm() {
            assert_reduces_to(
                "{a!(#{1|2|2}#) | c!(2) | for(b <- a & e <- c){count(*(b), *(e))}}",
                "2",
            );
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
            assert_reduces_to("{float(3, 64)}", "3");
        }
        #[test]
        fn bool_to_int_true() {
            assert_reduces_to("{int(true, 64)}", "1");
        }
        #[test]
        fn bool_to_int_false() {
            assert_reduces_to("{int(false, 64)}", "0");
        }
        #[test]
        fn int_to_str() {
            assert_reduces_to(r#"{str(42)}"#, r#""42""#);
        }

        #[test]
        fn int_from_bigint_fits_i64() {
            assert_reduces_to("{int(99n, 64)}", "99");
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

    fn assert_query_desugars(sugar_src: &str, rhs_src: &str, msg: &str) {
        fresh();
        let sugar = parse(sugar_src).normalize();
        let rhs = parse(rhs_src).normalize();
        assert!(sugar.term_eq(&rhs), "{}", msg);
    }

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
    fn quote_bare_name() {
        let _ = run("{@x!(0) | x!(1)}");
    }
    #[test]
    fn drop() {
        let _ = run("*(@(0))");
    }
    #[test]
    fn drop_bare_name() {
        let _ = run("*x");
    }
    #[test]
    fn send() {
        let _ = run("x!(0)");
    }

    #[test]
    fn send_polyadic_is_list_sugar() {
        fresh();
        let poly = parse("x!(1, 2, 3)").normalize();
        let list = parse("x!([1, 2, 3])").normalize();
        assert!(poly.term_eq(&list), "expected polyadic send sugar to match list payload");
    }

    #[test]
    fn send_polyadic_two_args_is_list_sugar() {
        fresh();
        let poly = parse("x!(1, 2)").normalize();
        let list = parse("x!([1, 2])").normalize();
        assert!(poly.term_eq(&list), "expected 2-arg send sugar to match list payload");
    }

    #[test]
    fn query_receive_sugar_single() {
        assert_query_desugars(
            "for(p <- x!?(a, b)){p}",
            "new(r) in { { x!(*r, a, b) | for(p <- r){p} } }",
            "expected `!?` to desugar to `new` + send + receive",
        );
    }

    #[test]
    fn query_receive_sugar_zero_args() {
        assert_query_desugars(
            "for(p <- x!?()){p}",
            "new(r) in { { x!(*r) | for(p <- r){p} } }",
            "expected zero-arg `!?` to pass only return channel",
        );
    }

    #[test]
    fn query_receive_sugar_single_with_where() {
        assert_query_desugars(
            "for(p <- x!?(a, b) where p == ok){p}",
            "new(r) in { { x!(*r, a, b) | for(p <- r where p == ok){p} } }",
            "expected `!?` bind with where-guard to desugar through private return channel",
        );
    }

    #[test]
    fn query_receive_sugar_multiple_joins() {
        assert_query_desugars(
            "for(p <- x1!?(a1) & q <- x2!?(a2) & z <- c){z}",
            "new(r1, r2) in { { x1!(*r1, a1) | x2!(*r2, a2) | for(p <- r1 & q <- r2 & z <- c){z} } }",
            "expected multiple `!?` binds to desugar to multiple return channels",
        );
    }

    #[test]
    fn query_receive_sugar_mixed_join_with_plain_bind() {
        assert_query_desugars(
            "for(p <- x!?(a) & q <- c){q}",
            "new(r) in { { x!(*r, a) | for(p <- r & q <- c){q} } }",
            "expected `!?` bind to compose with plain join binds",
        );
    }

    #[test]
    fn query_receive_sugar_mixed_rows_with_plain_bind() {
        assert_query_desugars(
            "for(p <- x!?(a); q <- c){q}",
            "new(r) in { { x!(*r, a) | for(p <- r; q <- c){q} } }",
            "expected `!?` bind to compose with semicolon-separated rows",
        );
    }

    #[test]
    fn query_receive_sugar_one_arg() {
        assert_query_desugars(
            "for(p <- x!?(a)){p}",
            "new(r) in { { x!(*r, a) | for(p <- r){p} } }",
            "expected one-arg `!?` to include return channel then arg",
        );
    }

    #[test]
    fn query_receive_sugar_three_args() {
        assert_query_desugars(
            "for(p <- x!?(a, b, c)){p}",
            "new(r) in { { x!(*r, a, b, c) | for(p <- r){p} } }",
            "expected three-arg `!?` to preserve argument order",
        );
    }

    #[test]
    fn query_receive_sugar_parenthesized_channel() {
        let _ = parse("for(p <- (x)!?(a)){p}");
    }

    #[test]
    fn query_receive_sugar_quoted_name_lhs() {
        assert_query_desugars(
            "for(p <- x!?(a)){*(@(p))}",
            "new(r) in { { x!(*r, a) | for(p <- r){*(@(p))} } }",
            "expected quoted name use in body to survive query desugaring",
        );
    }

    #[test]
    fn query_receive_sugar_two_queries_and_plain_join() {
        assert_query_desugars(
            "for(p <- x1!?(a1) & q <- x2!?(a2) & z <- c){z}",
            "new(r1, r2) in { { x1!(*r1, a1) | x2!(*r2, a2) | for(p <- r1 & q <- r2 & z <- c){z} } }",
            "expected multiple query binds to coexist with plain joins",
        );
    }

    #[test]
    fn query_receive_sugar_two_queries_with_where() {
        assert_query_desugars(
            "for(p <- x1!?(a1) & q <- x2!?(a2) where p == q){p}",
            "new(r1, r2) in { { x1!(*r1, a1) | x2!(*r2, a2) | for(p <- r1 & q <- r2 where p == q){p} } }",
            "expected where guard to remain attached after query desugaring",
        );
    }

    #[test]
    fn query_receive_sugar_three_queries_join() {
        assert_query_desugars(
            "for(p <- x1!?(a1) & q <- x2!?(a2) & t <- x3!?(a3)){t}",
            "new(r1, r2, r3) in { { x1!(*r1, a1) | x2!(*r2, a2) | x3!(*r3, a3) | for(p <- r1 & q <- r2 & t <- r3){t} } }",
            "expected three query binds to produce three private return channels",
        );
    }

    #[test]
    fn query_receive_sugar_join_row_then_plain_row() {
        assert_query_desugars(
            "for(p <- x1!?(a1) & q <- x2!?(a2); z <- c){z}",
            "new(r1, r2) in { { x1!(*r1, a1) | x2!(*r2, a2) | for(p <- r1 & q <- r2; z <- c){z} } }",
            "expected semicolon rows to remain in order after query desugaring",
        );
    }

    #[test]
    fn query_receive_sugar_plain_row_then_join_row() {
        assert_query_desugars(
            "for(z <- c; p <- x1!?(a1) & q <- x2!?(a2)){z}",
            "new(r1, r2) in { { x1!(*r1, a1) | x2!(*r2, a2) | for(z <- c; p <- r1 & q <- r2){z} } }",
            "expected query desugaring in later row to preserve earlier plain row",
        );
    }

    #[test]
    fn query_receive_sugar_two_query_rows() {
        assert_query_desugars(
            "for(p <- x1!?(a1); q <- x2!?(a2)){q}",
            "new(r1, r2) in { { x1!(*r1, a1) | x2!(*r2, a2) | for(p <- r1; q <- r2){q} } }",
            "expected query binds across rows to allocate independent return channels",
        );
    }

    #[test]
    fn query_receive_sugar_zero_args_in_join() {
        assert_query_desugars(
            "for(p <- x!?() & q <- c){q}",
            "new(r) in { { x!(*r) | for(p <- r & q <- c){q} } }",
            "expected zero-arg query bind to compose with join rows",
        );
    }

    #[test]
    fn query_receive_sugar_two_zero_arg_queries() {
        assert_query_desugars(
            "for(p <- x1!?() & q <- x2!?()){p}",
            "new(r1, r2) in { { x1!(*r1) | x2!(*r2) | for(p <- r1 & q <- r2){p} } }",
            "expected each zero-arg query bind to allocate return channel",
        );
    }

    #[test]
    fn query_receive_sugar_zero_args_with_where() {
        assert_query_desugars(
            "for(p <- x!?() where p == ok){p}",
            "new(r) in { { x!(*r) | for(p <- r where p == ok){p} } }",
            "expected where guard to work with zero-arg query bind",
        );
    }

    #[test]
    fn query_receive_sugar_with_arithmetic_guard() {
        assert_query_desugars(
            "for(p <- x!?(a) where p + 1 > 0){p}",
            "new(r) in { { x!(*r, a) | for(p <- r where p + 1 > 0){p} } }",
            "expected arithmetic guard to be preserved after desugaring",
        );
    }

    #[test]
    fn query_receive_sugar_with_boolean_guard() {
        assert_query_desugars(
            "for(p <- x!?(a) where p == ok and true){p}",
            "new(r) in { { x!(*r, a) | for(p <- r where p == ok and true){p} } }",
            "expected boolean guard structure to be preserved",
        );
    }

    #[test]
    fn query_receive_sugar_with_string_guard() {
        assert_query_desugars(
            "for(p <- x!?(a) where p == \"ok\"){p}",
            "new(r) in { { x!(*r, a) | for(p <- r where p == \"ok\"){p} } }",
            "expected string equality guard to survive desugaring",
        );
    }

    #[test]
    fn query_receive_sugar_with_list_arg() {
        assert_query_desugars(
            "for(p <- x!?([1,2,3])){p}",
            "new(r) in { { x!(*r, [1,2,3]) | for(p <- r){p} } }",
            "expected list argument to remain unchanged in query send",
        );
    }

    #[test]
    fn query_receive_sugar_with_map_arg() {
        assert_query_desugars(
            "for(p <- x!?(map(1:2, 3:4))){p}",
            "new(r) in { { x!(*r, map(1:2, 3:4)) | for(p <- r){p} } }",
            "expected map argument to remain unchanged in query send",
        );
    }

    #[test]
    fn query_receive_sugar_with_bag_arg() {
        assert_query_desugars(
            "for(p <- x!?(#{1|2}#)){p}",
            "new(r) in { { x!(*r, #{1|2}#) | for(p <- r){p} } }",
            "expected bag argument to remain unchanged in query send",
        );
    }

    #[test]
    fn query_receive_sugar_body_uses_bound_name() {
        assert_query_desugars(
            "for(p <- x!?(a)){*p}",
            "new(r) in { { x!(*r, a) | for(p <- r){*p} } }",
            "expected body to keep bound name usage after desugaring",
        );
    }

    #[test]
    fn query_receive_sugar_body_parallel_structure() {
        assert_query_desugars(
            "for(p <- x!?(a)){{*p | ok}}",
            "new(r) in { { x!(*r, a) | for(p <- r){{*p | ok}} } }",
            "expected body parallel structure to be preserved",
        );
    }

    #[test]
    fn query_receive_sugar_with_new_in_body() {
        assert_query_desugars(
            "for(p <- x!?(a)){new(k) in {k!(0)}}",
            "new(r) in { { x!(*r, a) | for(p <- r){new(k) in {k!(0)}} } }",
            "expected nested new in body to be preserved",
        );
    }

    #[test]
    fn query_receive_sugar_rows_with_where_and_plain_followup() {
        assert_query_desugars(
            "for(p <- x!?(a) & q <- y!?(b) where p == q; z <- c){z}",
            "new(r1, r2) in { { x!(*r1, a) | y!(*r2, b) | for(p <- r1 & q <- r2 where p == q; z <- c){z} } }",
            "expected mixed where+row composition to survive desugaring",
        );
    }

    #[test]
    fn query_receive_sugar_plain_then_query_with_where() {
        assert_query_desugars(
            "for(z <- c; p <- x!?(a) where p == ok){z}",
            "new(r) in { { x!(*r, a) | for(z <- c; p <- r where p == ok){z} } }",
            "expected where guard in later query row to be preserved",
        );
    }

    #[test]
    fn query_receive_sugar_three_rows_two_queries_one_plain() {
        assert_query_desugars(
            "for(p <- x!?(a); q <- c; r <- y!?(b)){q}",
            "new(r1, r2) in { { x!(*r1, a) | y!(*r2, b) | for(p <- r1; q <- c; r <- r2){q} } }",
            "expected multi-row ordering with two queries to be preserved",
        );
    }
    #[test]
    fn receive() {
        let _ = run("for(y <- x){y!(0)}");
    }
    #[test]
    fn multi_input() {
        let _ = run("{for(x <- c1 & y <- c2){*(x)} | c1!(p) | c2!(q)}");
    }

    #[test]
    fn old_receive_syntax_rejected() {
        let lang = RhoCalcLanguage;
        assert!(lang.parse_term("(c?x).{x!(0)}").is_err());
        assert!(lang.parse_term("(c1?x, c2?y).{*(x)}").is_err());
    }

    #[test]
    fn for_structural_pattern_requires_quote() {
        let lang = RhoCalcLanguage;
        assert!(lang.parse_term("for([1,2,4] <- c){7}").is_err());
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
// Numeric casts (`int`, `uint`, … on Proc)
// ════════════════════════════════════════════════════════════════════════════════

#[test]
fn rhocalc_cast_int_float_floor() {
    let results = run("{int(-3.5, 8)}");
    let nfs = normal_form_displays(&results);
    assert!(
        nfs.iter().any(|nf| nf == "-4" || nf.contains("-4")),
        "expected -4, got {:?}",
        nfs
    );
}

#[test]
fn rhocalc_cast_int_invalid_width_error() {
    let results = run("{int(1, 7)}");
    let nfs = normal_form_displays(&results);
    assert!(
        nfs.iter().any(|d| d == "error" || d.contains("error")),
        "expected error NF, got {:?}",
        nfs
    );
}

#[test]
fn rhocalc_cast_int_nonfinite_float_is_error() {
    let results = run("{int(0.0 / 0.0, 8)}");
    let nfs = normal_form_displays(&results);
    assert!(
        nfs.iter().any(|d| d == "error" || d.contains("error")),
        "expected error for NaN source, got {:?}",
        nfs
    );
}

#[test]
fn rhocalc_cast_uint_float_clamp() {
    let results = run("{uint(-3.5, 8)}");
    let nfs = normal_form_displays(&results);
    assert!(
        nfs.iter().any(|nf| nf == "0u32" || nf == "0"),
        "expected 0 / 0u32, got {:?}",
        nfs
    );
}

#[test]
fn rhocalc_cast_uint_modular_u32_literal() {
    let results = run("{uint(257u32, 8)}");
    let nfs = normal_form_displays(&results);
    assert!(
        nfs.iter().any(|nf| nf == "1u32" || nf == "1"),
        "expected modular 257 -> 1 in 8 bits, got {:?}",
        nfs
    );
}

#[test]
fn rhocalc_cast_float_overflow_to_inf() {
    let results = run("{float(1e50, 32)}");
    let nfs = normal_form_displays(&results);
    assert!(
        nfs.iter().any(|nf| nf.to_ascii_lowercase().contains("inf")),
        "expected +Inf in a normal form, got {:?}",
        nfs
    );
}

#[test]
fn rhocalc_cast_float_from_rational_string() {
    let results = run(r#"{float("1r/2r", 32)}"#);
    let nfs = normal_form_displays(&results);
    assert!(nfs.iter().any(|nf| nf == "0.5"), "expected 0.5 in a normal form, got {:?}", nfs);
}

#[test]
fn rhocalc_cast_float_from_bigint_n_string() {
    assert_reduces_to(r#"{float("1000n", 64)}"#, "1000");
}

#[test]
fn rhocalc_cast_float_from_fixed_p_string() {
    assert_reduces_to(r#"{float("1000.1p1", 64)}"#, "1000.1");
}

#[test]
fn rhocalc_casts_from_numeric_strings() {
    assert_reduces_to(r#"{int("2r/3r", 32)}"#, "0");
    assert_reduces_to(r#"{int("123n", 64)}"#, "123");
    assert_reduces_to(r#"{int("123i64", 64)}"#, "123");
    assert_reduces_to(r#"{int("10i32", 32)}"#, "10");
    assert_reduces_to(r#"{int("false", 32)}"#, "0");
    assert_reduces_to(r#"{int("true", 32)}"#, "1");
    assert_reduces_to(r#"{bigint("123n")}"#, "123");
    assert_reduces_to(r#"{bigrat("1r/2r")}"#, "1/2");
}

#[test]
fn rhocalc_str_from_rational_literal() {
    assert_reduces_to(r#"{str(23r)}"#, r#""23""#);
}

#[test]
fn rhocalc_bigint_unary_from_float() {
    let results = run("{bigint(-3.5)}");
    let nfs = normal_form_displays(&results);
    assert!(nfs.iter().any(|nf| nf.contains("-4")), "expected -4n or similar, got {:?}", nfs);
}

#[test]
fn rhocalc_cast_fixed_floor() {
    let results = run("{fixed(3.49p2, 1)}");
    let nfs = normal_form_displays(&results);
    assert!(
        nfs.iter()
            .any(|nf| nf.contains("3.4p1") || nf.contains("3.4")),
        "expected 3.4p1, got {:?}",
        nfs
    );
}

#[test]
fn rhocalc_cast_int_congruence_through_add() {
    assert_reduces_to("{int({1 + 2}, 8)}", "3");
}

#[test]
fn rhocalc_cast_uint_signed_int_twos_complement() {
    // `bitnot 0` → −1 (`CastInt`). Nesting `bitnot` inside an inner `{…}` PPar can block cast folds;
    // use it directly as the first operand of `uint`.
    assert_reduces_to("{uint(bitnot 0, 8)}", "255");
}

#[test]
fn rhocalc_cast_under_send_reduces_via_comm() {
    let results = run("{for(x <- c){*(x)} | c!({int(-3.5, 8)})}");
    let nfs = normal_form_displays(&results);
    assert!(
        nfs.iter().any(|nf| nf == "-4" || nf.contains("-4")),
        "expected `-4` after comm + cast in send, got {:?}",
        nfs
    );
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
        let term = lang.parse_term("for(y <- x){*(y)}").expect("parse");
        let var_types = lang.infer_var_types(term.as_ref());
        let y_info = var_types.iter().find(|v| v.name == "y");
        assert!(y_info.is_some(), "y should be found, got: {:?}", var_types);
        assert_eq!(format!("{}", y_info.unwrap().ty), "Name");
    }

    #[test]
    fn pinputs_lookup_by_name() {
        fresh();
        let lang = RhoCalcLanguage;
        let term = lang.parse_term("for(y <- x){*(y)}").expect("parse");
        let y_type = lang.infer_var_type(term.as_ref(), "y");
        assert!(y_type.is_some());
        assert_eq!(format!("{}", y_type.unwrap()), "Name");
    }

    #[test]
    fn multi_input_infers_both_vars() {
        fresh();
        let lang = RhoCalcLanguage;
        let term = lang
            .parse_term("for(x <- c1 & y <- c2){*(x)}")
            .expect("parse");
        let var_types = lang.infer_var_types(term.as_ref());
        assert!(var_types.iter().any(|v| v.name == "x"));
        assert!(var_types.iter().any(|v| v.name == "y"));
    }
}
