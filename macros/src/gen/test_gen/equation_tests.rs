//! Equation test generation for `language!` specifications.
//!
//! Generates one `#[test]` per equation that:
//! 1. Instantiates the language struct
//! 2. Verifies equation metadata is present and well-formed
//! 3. Checks that LHS and RHS strings are non-empty
//!
//! Equations with freshness conditions cannot be instantiated without concrete
//! substitutions, so they get a metadata-presence test only (not `#[ignore]`d).
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
            // ★★ #150 — THE SIBLING OF `rewrite_tests.rs`'s CONGRUENCE BRANCH, and the comment
            // it used to carry was a statement about a body it did not have.
            //
            // It read *"so emit a metadata-presence test only"* above a body containing NO
            // metadata check: `let _lang = X;` and two prose lines. Six such tests shipped
            // (Rholang's `Extrude`, five in Ambient). Now the comment is true — the presence test
            // is emitted, and so is the FACT that justifies the skip: a freshness / `ForAll` /
            // guard / relation premise really is reflected in `eq.conditions`.
            //
            // `EquationDef::conditions` is built from `eq.premises` by the same walk this branch
            // classified (`macros/src/gen/runtime/metadata.rs:792`), so an empty `conditions`
            // beneath a `has_complex_premises` verdict means the two disagree — which is the only
            // way this disposition can be wrong. Pinned by
            // `languages/tests/generated_tests_assert_something.rs`.
            out.push_str(&format!(
                "// Equation {} carries a freshness/ForAll/guard/relation premise: not \
                 instantiated\n\
                 \x20// here. Its disposition is asserted instead — metadata presence + the \
                 premise\n\
                 \x20// that IS the reason it is not instantiated.\n",
                eq_name
            ));
            out.push_str("#[test]\n");
            out.push_str(&format!("fn {}() {{\n", test_name));
            out.push_str(&format!("    let _lang = {};\n", lang_struct));
            out.push_str("    let meta = _lang.metadata();\n");
            out.push_str("    let equations = meta.equations();\n");
            out.push_str(&format!(
                "    assert!(\n\
                 \x20       equations.len() > {},\n\
                 \x20       \"Expected at least {} equations in metadata, found {{}}\",\n\
                 \x20       equations.len()\n\
                 \x20   );\n\
                 \x20   let eq = &equations[{}];\n",
                i,
                i + 1,
                i
            ));
            out.push_str(&format!(
                "    assert_eq!(eq.name, \"{}\", \"Equation name mismatch\");\n\
                 \x20   assert!(!eq.lhs.is_empty(), \"Equation {} LHS should be non-empty\");\n\
                 \x20   assert!(!eq.rhs.is_empty(), \"Equation {} RHS should be non-empty\");\n",
                eq_name, eq_name, eq_name,
            ));
            out.push_str(&format!(
                "    // THE DISPOSITION: this branch was selected because the equation carries a\n\
                 \x20   // premise the static instantiator cannot discharge, so the reflected\n\
                 \x20   // metadata must show that premise.\n\
                 \x20   assert!(\n\
                 \x20       !eq.conditions.is_empty(),\n\
                 \x20       \"{} was skipped for freshness/complex premises, but its reflected \\\n\
                 \x20        metadata carries no conditions — the codegen predicate and the \\\n\
                 \x20        reflection disagree about its premises\"\n\
                 \x20   );\n",
                eq_name,
            ));
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
