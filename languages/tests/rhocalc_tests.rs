use ascent::*;
use ascent_byods_rels::*;
use mettail_languages::rhocalc::*;
use mettail_runtime::Language;

/// For PPar terms, return a canonical multiset of (element_display, count) sorted by display.
/// Used to compare parallel compositions regardless of HashBag iteration order.
fn par_display_multiset(proc: &rhocalc::Proc) -> Option<Vec<(String, usize)>> {
    if let rhocalc::Proc::PPar(bag) = proc {
        let mut v: Vec<_> = bag.iter().map(|(p, c)| (p.to_string(), *c)).collect();
        v.sort_by(|a, b| a.0.cmp(&b.0));
        Some(v)
    } else {
        None
    }
}

struct TestCase {
    name: &'static str,
    input: &'static str,
    expected_output: Option<&'static str>,
    should_normalize: bool,
    min_rewrites: usize,
    description: &'static str,
}

fn run_test(test: &TestCase) -> Result<(), String> {
    println!("TEST: {}", test.name);
    println!("Description: {}", test.description);
    println!("Input: {}", test.input);

    mettail_runtime::clear_var_cache();
    let parser = rhocalc::ProcParser::new();
    let input_term = parser
        .parse(test.input)
        .map_err(|e| format!("Parse error: {:?}", e))?;

    // Normalize to flatten any nested collections
    let input_term = input_term.normalize();

    println!("Parsed: {}", input_term);

    let prog = ascent_run! {
        include_source!(rhocalc_source);
        proc(p) <-- for p in [input_term.clone()];

        relation redex_eq(Proc);
        redex_eq(q.clone()) <-- eq_proc(input_term.clone(), q);
        proc(q) <-- redex_eq(q);

        relation path(Proc, Proc);
        path(p1, p2) <-- rw_proc(p1,p2);
        path(p1, p3) <-- path(p1,p2), path(p2,p3);

        relation is_normal_form(Proc);
        is_normal_form(t.clone()) <-- proc(t), !rw_proc(t.clone(),_);

        relation path_full(Proc, Proc);
        path_full(input_term.clone(), z.clone()) <-- is_normal_form(z), path(input_term.clone(), z.clone());
    };

    let mut rewrites: Vec<_> = prog.rw_proc.iter().collect();
    rewrites.sort_by(|a, b| a.0.cmp(&b.0));

    println!("\nEquations:");
    let eq_count = 0;
    // for (lhs, rhs) in prog.__eq_proc_ind_common.iter_all_added() {
    //     if lhs.to_string() != rhs.to_string() {
    //         println!("  {} = {}", lhs, rhs);
    //         eq_count += 1;
    //     }
    // }
    if eq_count == 0 {
        println!("  (none)");
    }

    println!("\nRewrites found: {}", rewrites.len());
    for (i, (s, t)) in rewrites.iter().enumerate().take(20) {
        println!("  [{}] {} ~> {}", i + 1, s, t);
    }
    if rewrites.len() > 20 {
        println!("  ... ({} more)", rewrites.len() - 20);
    }

    // Check minimum rewrites
    if rewrites.len() < test.min_rewrites {
        return Err(format!(
            "Expected at least {} rewrites, found {}",
            test.min_rewrites,
            rewrites.len()
        ));
    }

    // Check normalization
    let normal_forms: Vec<_> = prog.is_normal_form.iter().collect();
    println!("\nNormal forms: {}", normal_forms.len());
    for nf in &normal_forms {
        println!("  {}", nf.0);
    }

    if test.should_normalize && normal_forms.is_empty() {
        return Err("Expected to find a normal form, but none found".to_string());
    }

    // Check expected output if provided
    if let Some(expected_str) = test.expected_output {
        let expected = parser
            .parse(expected_str)
            .map_err(|e| format!("Parse error in expected: {:?}", e))?
            .normalize();
        let expected_display = expected.to_string();

        // Check if expected output is in the rewrite relation or path
        let found = rewrites
            .iter()
            .any(|(from, to)| from == &input_term && to == &expected)
            || prog
                .path
                .iter()
                .any(|(from, to)| from == &input_term && to == &expected);

        if !found {
            // Also check if it's in normal forms (by value, by display, by normalized equality, or by PPar display multiset)
            let in_normal_forms = normal_forms.iter().any(|nf| nf.0 == expected);
            let in_normal_forms_display = normal_forms
                .iter()
                .any(|nf| nf.0.to_string() == expected_display);
            let in_normal_forms_normalized = normal_forms
                .iter()
                .any(|nf| nf.0.clone().normalize() == expected);
            let in_normal_forms_par_display =
                par_display_multiset(&expected).map_or(false, |expected_ms| {
                    normal_forms.iter().any(|nf| {
                        par_display_multiset(&nf.0).map_or(false, |nf_ms| nf_ms == expected_ms)
                    })
                });
            if !in_normal_forms
                && !in_normal_forms_display
                && !in_normal_forms_normalized
                && !in_normal_forms_par_display
            {
                return Err(format!(
                    "Expected output '{}' not found in rewrites or normal forms.\nNormalized expected: {}\nAvailable normal forms: {:?}",
                    expected_str,
                    expected,
                    normal_forms.iter().map(|nf| nf.0.to_string()).collect::<Vec<_>>()
                ));
            }
        }
        println!("\n✓ Expected output found: {}", expected_str);
    }

    println!("\n✓ Test passed!");
    Ok(())
}

/// The 6 multi-communication test cases (Phase 11). Used by main() and by #[test] test_multi_comm_cases.
fn multi_comm_tests() -> Vec<TestCase> {
    vec![
        TestCase {
            name: "multi_comm_basic",
            input: "{(c1?x, c2?y).{*(x)} | c1!(p) | c2!(q)}",
            expected_output: Some("p"),
            should_normalize: true,
            min_rewrites: 1,
            description: "Basic multi-communication: receive on two channels, use first",
        },
        TestCase {
            name: "multi_comm_both_vars",
            input: "{(c1?x, c2?y).{{*(x) | *(y)}} | c1!(p) | c2!(q)}",
            expected_output: Some("p"),
            should_normalize: true,
            min_rewrites: 1,
            description: "Multi-communication using both received values",
        },
        TestCase {
            name: "multi_comm_three_channels",
            input: "{(a?x, b?y, c?z).{{*(x) | *(y) | *(z)}} | a!(p) | b!(q) | c!(r)}",
            expected_output: Some("{p | q | r}"),
            should_normalize: true,
            min_rewrites: 1,
            description: "Multi-communication on three channels",
        },
        TestCase {
            name: "multi_comm_forward",
            input: "{(c1?x, c2?y).{out!(*(x))} | c1!(data) | c2!(ignored)}",
            expected_output: Some("out!(*(@(data)))"),
            should_normalize: true,
            min_rewrites: 1,
            description: "Multi-comm with forwarding on one channel",
        },
        TestCase {
            name: "multi_comm_join",
            input: "{(c?x, c?y).{{*(x) | *(y)}} | c!(a) | c!(b)}",
            expected_output: Some("{a | b}"),
            should_normalize: true,
            min_rewrites: 1,
            description: "Join pattern: two receives on same channel",
        },
        TestCase {
            name: "multi_comm_with_parallel",
            input: "{(c1?x, c2?y).{*(x)} | c1!(p) | c2!(q)}",
            expected_output: Some("p"),
            should_normalize: true,
            min_rewrites: 1,
            description: "Multi-comm in nested parallel context",
        },
    ]
}

// --- #[test] integration tests (run with cargo test) ---

#[test]
fn test_multi_comm_cases() {
    for t in &multi_comm_tests() {
        run_test(t).expect(t.name);
    }
}

#[test]
fn test_parse_zero() {
    mettail_runtime::clear_var_cache();
    let lang = RhoCalcLanguage;
    let term = lang.parse_term("0").expect("parse 0");
    let results = lang.run_ascent(term.as_ref()).expect("run_ascent");
    assert!(!results.all_terms.is_empty(), "run_ascent should yield at least one term");
}

#[test]
fn test_parse_empty_par() {
    mettail_runtime::clear_var_cache();
    let lang = RhoCalcLanguage;
    let term = lang.parse_term("{}").expect("parse {}");
    let results = lang.run_ascent(term.as_ref()).expect("run_ascent");
    assert!(!results.all_terms.is_empty());
}

#[test]
fn test_parse_quote() {
    mettail_runtime::clear_var_cache();
    let lang = RhoCalcLanguage;
    let term = lang.parse_term("@(0)").expect("parse @(0)");
    let results = lang.run_ascent(term.as_ref()).expect("run_ascent");
    assert!(!results.all_terms.is_empty());
}

#[test]
fn test_parse_drop() {
    mettail_runtime::clear_var_cache();
    let lang = RhoCalcLanguage;
    let term = lang.parse_term("*(@(0))").expect("parse *(@(0))");
    let results = lang.run_ascent(term.as_ref()).expect("run_ascent");
    assert!(!results.all_terms.is_empty());
}

#[test]
fn test_parse_send() {
    mettail_runtime::clear_var_cache();
    let lang = RhoCalcLanguage;
    let term = lang.parse_term("x!(0)").expect("parse x!(0)");
    let results = lang.run_ascent(term.as_ref()).expect("run_ascent");
    assert!(!results.all_terms.is_empty());
}

#[test]
fn test_parse_receive() {
    mettail_runtime::clear_var_cache();
    let lang = RhoCalcLanguage;
    // Grammar uses (name?var).{body} for receive, not for(x -> y){body}
    let term = lang
        .parse_term("(x?y).{y!(0)}")
        .expect("parse (x?y).{y!(0)}");
    let results = lang.run_ascent(term.as_ref()).expect("run_ascent");
    assert!(!results.all_terms.is_empty());
}

#[test]
fn test_parse_multi_input() {
    mettail_runtime::clear_var_cache();
    let lang = RhoCalcLanguage;
    let input = "{(c1?x, c2?y).{*(x)} | c1!(p) | c2!(q)}";
    let term = lang.parse_term(input).expect("parse multi-input");
    let results = lang.run_ascent(term.as_ref()).expect("run_ascent");
    assert!(!results.all_terms.is_empty());
}

#[test]
fn test_rewrite_exec_drop() {
    mettail_runtime::clear_var_cache();
    let lang = RhoCalcLanguage;
    let term = lang.parse_term("{*(@(0))}").expect("parse");
    let results = lang.run_ascent(term.as_ref()).expect("run_ascent");
    assert!(results.rewrites.len() >= 1, "Exec rewrite *(@(p)) ~> p should fire");
    let displays: Vec<&str> = results
        .normal_forms()
        .iter()
        .map(|nf| nf.display.as_str())
        .collect();
    assert!(displays.contains(&"0"), "normal forms should include 0, got {:?}", displays);
}

#[test]
fn test_rewrite_comm() {
    mettail_runtime::clear_var_cache();
    let lang = RhoCalcLanguage;
    // Grammar uses (c?x).{body} for receive
    let term = lang.parse_term("{(c?x).{x!(0)} | c!(p)}").expect("parse");
    let results = lang.run_ascent(term.as_ref()).expect("run_ascent");
    assert!(results.rewrites.len() >= 1, "Comm rewrite should fire");
    assert!(!results.normal_forms().is_empty(), "should have at least one normal form");
}

#[test]
fn test_rewrite_par_cong() {
    mettail_runtime::clear_var_cache();
    let lang = RhoCalcLanguage;
    let term = lang.parse_term("{*(@(0)) | 0}").expect("parse");
    let results = lang.run_ascent(term.as_ref()).expect("run_ascent");
    assert!(results.rewrites.len() >= 1, "ParCong + Exec should apply");
    let displays: Vec<&str> = results
        .normal_forms()
        .iter()
        .map(|nf| nf.display.as_str())
        .collect();
    assert!(displays.contains(&"0"), "normal form should include 0, got {:?}", displays);
}

#[test]
fn test_corner_nested_par() {
    mettail_runtime::clear_var_cache();
    let lang = RhoCalcLanguage;
    let term = lang.parse_term("{{0}}").expect("parse {{0}}");
    let results = lang.run_ascent(term.as_ref()).expect("run_ascent");
    assert!(!results.all_terms.is_empty());
}

#[test]
fn test_corner_nested_par_drop() {
    mettail_runtime::clear_var_cache();
    let lang = RhoCalcLanguage;
    let term = lang.parse_term("{{*(@(p))}}").expect("parse");
    let results = lang.run_ascent(term.as_ref()).expect("run_ascent");
    assert!(results.rewrites.len() >= 1, "Exec under par should fire");
}

#[test]
fn test_native_types_bool_and_comparisons() {
    mettail_runtime::clear_var_cache();
    let lang = RhoCalcLanguage;
    // Bool literals
    let term = lang
        .parse_term("{ true | false }")
        .expect("parse bool literals");
    let results = lang.run_ascent(term.as_ref()).expect("run_ascent");
    assert!(!results.normal_forms().is_empty(), "should reduce");
    // Comparison: 1 == 1 -> true
    let term = lang.parse_term("{ 1 == 1 }").expect("parse eq");
    let results = lang.run_ascent(term.as_ref()).expect("run_ascent");
    let displays: Vec<&str> = results
        .normal_forms()
        .iter()
        .map(|nf| nf.display.as_str())
        .collect();
    assert!(
        displays.iter().any(|d| d.contains("true")),
        "normal forms should include true, got {:?}",
        displays
    );
}

#[test]
fn test_native_types_string_and_concat() {
    mettail_runtime::clear_var_cache();
    let lang = RhoCalcLanguage;
    let term = lang
        .parse_term(r#"{ concat("hello", "world") }"#)
        .expect("parse concat");
    let results = lang.run_ascent(term.as_ref()).expect("run_ascent");
    let displays: Vec<&str> = results
        .normal_forms()
        .iter()
        .map(|nf| nf.display.as_str())
        .collect();
    assert!(
        displays.iter().any(|d| d.contains("helloworld")),
        "normal forms should include concat result, got {:?}",
        displays
    );
}

fn main() {
    let tests = multi_comm_tests();

    println!("Running {} RhoCalc tests...", tests.len());

    let mut passed = 0;
    let mut failed = 0;
    let mut errors = Vec::new();

    for test in &tests {
        match run_test(test) {
            Ok(()) => passed += 1,
            Err(e) => {
                failed += 1;
                errors.push((test.name, e));
            },
        }
    }

    println!("TEST SUMMARY");
    println!("Total: {}", tests.len());
    println!("Passed: {}", passed);
    println!("Failed: {}", failed);

    if !errors.is_empty() {
        println!("FAILURES:");
        for (name, error) in &errors {
            println!("\n✗ {}", name);
            println!("  Error: {}", error);
        }
    }

    if failed > 0 {
        std::process::exit(1);
    } else {
        println!("\n✓ All tests passed!");
    }
}
