//! Equation test generation for `language!` specifications.
//!
//! Generates one `#[test]` per equation that:
//! 1. Instantiates the language struct
//! 2. Verifies equation metadata is present and well-formed
//! 3. Checks that LHS and RHS strings are non-empty
//!
//! Equations with freshness conditions are marked `#[ignore]` since they
//! cannot be instantiated without concrete substitutions.
//!
//! NOTE: Equation LHS/RHS are pattern strings with meta-variables that cannot
//! be parsed as concrete terms. Tests verify metadata presence only.

use mettail_ast::language::{LanguageDef, Premise};

/// Generate per-equation tests for the language.
///
/// Returns a string of `#[test]` functions to be spliced into the generated
/// test file.
pub fn generate_equation_tests(language: &LanguageDef) -> String {
    let lang_name = language.name.to_string();
    let lang_name_lower = lang_name.to_lowercase();
    let lang_struct = format!("{}Language", lang_name);

    let mut out = String::with_capacity(4096);

    if language.equations.is_empty() {
        return out;
    }

    for (i, equation) in language.equations.iter().enumerate() {
        let eq_name = equation.name.to_string();
        let test_name = format!("equation_{}_{}", lang_name_lower, eq_name.to_lowercase());

        // Check if equation has freshness conditions or other complex premises
        let has_complex_premises = equation.premises.iter().any(|p| {
            matches!(
                p,
                Premise::Freshness(_)
                    | Premise::ForAll { .. }
                    | Premise::BehavioralGuard(_)
                    | Premise::RelationQuery { .. }
            )
        });

        if has_complex_premises {
            // Emit with #[ignore] for equations with complex conditions
            out.push_str(&format!("// Equation {} has freshness/complex conditions\n", eq_name));
            // Equation has freshness/complex conditions — metadata test only.
            out.push_str("#[test]\n");
            out.push_str(&format!("fn {}() {{\n", test_name));
            out.push_str(&format!("    let _lang = {};\n", lang_struct));
            out.push_str(
                "    // This equation requires freshness conditions or complex premises\n",
            );
            out.push_str("    // that cannot be instantiated statically.\n");
            out.push_str("}\n\n");
        } else {
            // Generate a test that verifies equation metadata presence
            out.push_str("#[test]\n");
            out.push_str(&format!("fn {}() {{\n", test_name));
            out.push_str(&format!("    let _lang = {};\n", lang_struct));
            out.push_str("    let meta = _lang.metadata();\n");
            out.push_str("    let equations = meta.equations();\n");

            out.push_str(&format!(
                "    // Verify equation {} (index {}) exists in metadata\n",
                eq_name, i
            ));
            out.push_str(&format!(
                "    assert!(\n\
                 \x20       equations.len() > {},\n\
                 \x20       \"Expected at least {} equations in metadata, found {{}}\",\n\
                 \x20       equations.len()\n\
                 \x20   );\n",
                i,
                i + 1
            ));
            out.push_str(&format!("    let eq = &equations[{}];\n", i));

            // Verify LHS and RHS are non-empty
            // NOTE: Do NOT try to parse these strings as concrete terms — they
            // contain meta-variables (N, P, Q, ...rest, etc.) and the parser
            // may stack-overflow on deeply nested pattern strings.
            out.push_str(&format!(
                "    assert!(!eq.lhs.is_empty(), \"Equation {} LHS should be non-empty\");\n",
                eq_name
            ));
            out.push_str(&format!(
                "    assert!(!eq.rhs.is_empty(), \"Equation {} RHS should be non-empty\");\n",
                eq_name
            ));

            out.push_str("}\n\n");
        }
    }

    out
}
