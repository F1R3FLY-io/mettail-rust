//! Test function string generation for operational semantics tests.
//!
//! Generates `#[test]` function source code for each ground term + expected result pair.
//! When the symbolic evaluator can compute an expected result, generates an assertion test.
//! When it cannot, generates a smoke test (just verifies execution completes and produces
//! at least one normal form).

/// A test case ready for code generation.
#[derive(Debug)]
pub struct TestCase {
    /// Full test function name (e.g., `eval_calculator_addint_1_2`).
    pub test_name: String,
    /// The Rust code to construct the input term.
    pub construction_code: String,
    /// The language struct name (e.g., `CalculatorLanguage`).
    pub lang_struct: String,
    /// Expected display string, or `None` for smoke tests.
    pub expected: Option<String>,
}

/// Generate a `#[test]` function string for a test case.
///
/// Uses iterative string building (no recursion).
pub fn generate_test_function(test: &TestCase) -> String {
    let mut out = String::with_capacity(512);

    out.push_str("#[test]\n");
    out.push_str(&format!("fn {}() {{\n", test.test_name));
    out.push_str("    mettail_runtime::clear_var_cache();\n");
    out.push_str(&format!(
        "    let input_term = {};\n",
        test.construction_code
    ));
    out.push_str("    let input_str = format!(\"{}\", input_term);\n");
    out.push_str(&format!("    let lang = {};\n", test.lang_struct));
    out.push_str(
        "    let parsed = lang.parse_term(&input_str).expect(\"parse should succeed\");\n",
    );
    out.push_str(
        "    let results = lang.run_ascent(parsed.as_ref()).expect(\"eval should succeed\");\n",
    );

    if let Some(expected) = &test.expected {
        // Full assertion test
        out.push_str(
            "    let nfs: Vec<String> = results.normal_forms().iter().map(|nf| nf.display.clone()).collect();\n",
        );
        // Escape the expected string for embedding in Rust source
        let escaped_expected = escape_rust_string(expected);
        out.push_str(&format!(
            "    assert!(nfs.iter().any(|d| d == \"{}\"),\n",
            escaped_expected
        ));
        out.push_str(&format!(
            "        \"{{}} should evaluate to {}, got {{:?}}\", input_str, nfs);\n",
            escaped_expected
        ));
    } else {
        // Smoke test
        out.push_str(
            "    assert!(!results.normal_forms().is_empty(),\n",
        );
        out.push_str(
            "        \"{} should evaluate to at least one normal form\", input_str);\n",
        );
    }

    out.push_str("}\n\n");
    out
}

/// Escape a string for embedding in a Rust string literal.
///
/// Handles: `\`, `"`, `\n`, `\t`, `\r`.
fn escape_rust_string(s: &str) -> String {
    let mut escaped = String::with_capacity(s.len() + 8);
    for ch in s.chars() {
        match ch {
            '\\' => escaped.push_str("\\\\"),
            '"' => escaped.push_str("\\\""),
            '\n' => escaped.push_str("\\n"),
            '\t' => escaped.push_str("\\t"),
            '\r' => escaped.push_str("\\r"),
            _ => escaped.push(ch),
        }
    }
    escaped
}

/// Generate all test functions from a list of test cases.
///
/// Returns a single string containing all `#[test]` functions.
pub fn generate_all_tests(tests: &[TestCase]) -> String {
    let estimated_size = tests.len() * 600;
    let mut out = String::with_capacity(estimated_size);

    // Iterative: just loop, no recursion
    for test in tests {
        out.push_str(&generate_test_function(test));
    }

    out
}
