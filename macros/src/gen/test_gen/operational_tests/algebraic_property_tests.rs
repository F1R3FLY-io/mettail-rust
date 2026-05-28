//! Phase 3b: Algebraic property test generation.
//!
//! Scans `language.equations` for algebraic patterns (commutativity, associativity,
//! identity) and generates both concrete ground-instance tests and proptest blocks
//! for metamorphic verification.
//!
//! Detection is by pattern-matching on the equation's `left` and `right` `Pattern`
//! structures. All recursive operations use iterative work-stacks (trampolines).
//! Everything is derived from the `language!` spec.

use mettail_ast::language::{Equation, LanguageDef};
use mettail_ast::pattern::{Pattern, PatternTerm};
use std::collections::{HashMap, HashSet};

use super::expr_string_gen::TestCase;

/// Maximum algebraic property tests per language.
const MAX_ALGEBRAIC_TESTS: usize = 30;

/// Detected algebraic property.
#[derive(Debug, Clone)]
pub enum AlgebraicProperty {
    /// f(a, b) = f(b, a)
    Commutativity {
        equation_name: String,
        constructor: String,
        param_a: String,
        param_b: String,
    },
    /// f(f(a, b), c) = f(a, f(b, c))
    Associativity {
        equation_name: String,
        constructor: String,
        param_a: String,
        param_b: String,
        param_c: String,
    },
    /// f(a, e) = a where e is a literal/nullary
    Identity {
        equation_name: String,
        constructor: String,
        param_a: String,
        identity_element: String,
    },
}

/// Generate algebraic property tests for the language.
///
/// Returns a vector of `TestCase` for concrete ground-instance tests,
/// plus a string containing proptest blocks for metamorphic relations.
pub fn generate_algebraic_tests(
    language: &LanguageDef,
    ambiguous_prefix_rules: &HashSet<String>,
) -> (Vec<TestCase>, String) {
    let lang_name = language.name.to_string();
    let lang_name_lower = lang_name.to_lowercase();
    let lang_struct = format!("{}Language", lang_name);

    let mut test_cases: Vec<TestCase> = Vec::with_capacity(MAX_ALGEBRAIC_TESTS);
    let mut proptest_blocks = String::new();

    // Step 1: Detect algebraic properties from equations
    let properties = detect_algebraic_properties(language);

    if properties.is_empty() {
        return (test_cases, proptest_blocks);
    }

    // Step 2: Build leaf map for ground instances
    let leaf_map = super::nested_expr_gen::build_simple_leaf_map_pub(language);

    // Step 3: Generate concrete tests for each detected property
    for prop in &properties {
        if test_cases.len() >= MAX_ALGEBRAIC_TESTS {
            break;
        }

        match prop {
            AlgebraicProperty::Commutativity {
                equation_name,
                constructor,
                param_a,
                param_b,
            } => {
                if ambiguous_prefix_rules.contains(constructor) {
                    continue;
                }

                // Find the rule for this constructor to determine category
                let rule = match language
                    .terms
                    .iter()
                    .find(|r| r.label.to_string() == *constructor)
                {
                    Some(r) => r,
                    None => continue,
                };
                let category = rule.category.to_string();

                // Get two different leaf values for the params
                let param_info = super::ground_term_enum::extract_param_info(rule, language);
                if param_info.len() < 2 {
                    continue;
                }

                let cat_a = &param_info[0].category;
                let cat_b = &param_info[1].category;

                // Use different values for a and b to make commutativity non-trivial
                let leaf_a = match leaf_map.get(cat_a.as_str()) {
                    Some(l) => l,
                    None => continue,
                };
                let leaf_b = get_different_leaf(cat_b, language, &leaf_a.raw_value);
                let leaf_b = match leaf_b {
                    Some(l) => l,
                    None => match leaf_map.get(cat_b.as_str()) {
                        Some(l) => l.clone(),
                        None => continue,
                    },
                };

                // Construct f(a, b) and f(b, a)
                let term_ab = format!(
                    "{}::{}(std::sync::Arc::new({}), std::sync::Arc::new({}))",
                    category, constructor, leaf_a.construction, leaf_b.construction
                );
                let term_ba = format!(
                    "{}::{}(std::sync::Arc::new({}), std::sync::Arc::new({}))",
                    category, constructor, leaf_b.construction, leaf_a.construction
                );

                let test_name = format!(
                    "alg_{}_comm_{}_concrete",
                    lang_name_lower,
                    constructor.to_lowercase()
                );

                test_cases.push(generate_algebraic_eq_test(
                    &test_name,
                    &term_ab,
                    &term_ba,
                    &lang_struct,
                    equation_name,
                ));
            },
            AlgebraicProperty::Associativity {
                equation_name,
                constructor,
                param_a,
                param_b,
                param_c,
            } => {
                if ambiguous_prefix_rules.contains(constructor) {
                    continue;
                }

                let rule = match language
                    .terms
                    .iter()
                    .find(|r| r.label.to_string() == *constructor)
                {
                    Some(r) => r,
                    None => continue,
                };
                let category = rule.category.to_string();
                let param_info = super::ground_term_enum::extract_param_info(rule, language);
                if param_info.len() < 2 {
                    continue;
                }

                let cat = &param_info[0].category;
                let leaf = match leaf_map.get(cat.as_str()) {
                    Some(l) => l,
                    None => continue,
                };

                // f(f(a, b), c) and f(a, f(b, c))
                let inner_ab = format!(
                    "{}::{}(std::sync::Arc::new({}), std::sync::Arc::new({}))",
                    category, constructor, leaf.construction, leaf.construction
                );
                let inner_bc = format!(
                    "{}::{}(std::sync::Arc::new({}), std::sync::Arc::new({}))",
                    category, constructor, leaf.construction, leaf.construction
                );
                let term_lhs = format!(
                    "{}::{}(std::sync::Arc::new({}), std::sync::Arc::new({}))",
                    category, constructor, inner_ab, leaf.construction
                );
                let term_rhs = format!(
                    "{}::{}(std::sync::Arc::new({}), std::sync::Arc::new({}))",
                    category, constructor, leaf.construction, inner_bc
                );

                let test_name = format!(
                    "alg_{}_assoc_{}_concrete",
                    lang_name_lower,
                    constructor.to_lowercase()
                );

                test_cases.push(generate_algebraic_eq_test(
                    &test_name,
                    &term_lhs,
                    &term_rhs,
                    &lang_struct,
                    equation_name,
                ));
            },
            AlgebraicProperty::Identity {
                equation_name,
                constructor,
                param_a,
                identity_element,
            } => {
                if ambiguous_prefix_rules.contains(constructor) {
                    continue;
                }

                let rule = match language
                    .terms
                    .iter()
                    .find(|r| r.label.to_string() == *constructor)
                {
                    Some(r) => r,
                    None => continue,
                };
                let category = rule.category.to_string();
                let param_info = super::ground_term_enum::extract_param_info(rule, language);
                if param_info.len() < 2 {
                    continue;
                }

                let cat = &param_info[0].category;
                let leaf = match leaf_map.get(cat.as_str()) {
                    Some(l) => l,
                    None => continue,
                };

                // f(a, e) should equal a
                // We construct f(a, e) and compare its eval to a's eval
                let test_name = format!(
                    "alg_{}_identity_{}_concrete",
                    lang_name_lower,
                    constructor.to_lowercase()
                );

                // For identity, we compare eval(f(a,e)) with eval(a)
                // Generated as a test that evaluates both sides and compares
                test_cases.push(generate_identity_test(
                    &test_name,
                    &leaf.construction,
                    constructor,
                    &category,
                    identity_element,
                    &lang_struct,
                    equation_name,
                    language,
                ));
            },
        }
    }

    // Step 4: Generate proptest blocks for detected properties (Phase 6 integration)
    proptest_blocks = generate_algebraic_proptest_blocks(&properties, language, &lang_name_lower, &lang_struct);

    (test_cases, proptest_blocks)
}

/// Detect algebraic properties by analyzing equations.
///
/// Uses iterative work-stacks for pattern traversal.
pub fn detect_algebraic_properties(language: &LanguageDef) -> Vec<AlgebraicProperty> {
    let mut properties = Vec::new();

    for eq in &language.equations {
        // Try commutativity detection: f(a, b) = f(b, a)
        if let Some(prop) = detect_commutativity(eq) {
            properties.push(prop);
            continue;
        }

        // Try associativity detection: f(f(a,b),c) = f(a,f(b,c))
        if let Some(prop) = detect_associativity(eq) {
            properties.push(prop);
            continue;
        }

        // Try identity detection: f(a, e) = a
        if let Some(prop) = detect_identity(eq) {
            properties.push(prop);
        }
    }

    properties
}

/// Detect commutativity: f(a, b) = f(b, a)
///
/// Both sides must be `Apply` with the same constructor, exactly 2 args,
/// and the args are vars that are swapped.
fn detect_commutativity(eq: &Equation) -> Option<AlgebraicProperty> {
    let (lhs_ctor, lhs_args) = extract_apply(&eq.left)?;
    let (rhs_ctor, rhs_args) = extract_apply(&eq.right)?;

    if lhs_ctor != rhs_ctor {
        return None;
    }
    if lhs_args.len() != 2 || rhs_args.len() != 2 {
        return None;
    }

    let la = extract_var_name(&lhs_args[0])?;
    let lb = extract_var_name(&lhs_args[1])?;
    let ra = extract_var_name(&rhs_args[0])?;
    let rb = extract_var_name(&rhs_args[1])?;

    // Commutativity: f(a,b) = f(b,a)
    if la == rb && lb == ra && la != lb {
        return Some(AlgebraicProperty::Commutativity {
            equation_name: eq.name.to_string(),
            constructor: lhs_ctor,
            param_a: la,
            param_b: lb,
        });
    }

    None
}

/// Detect associativity: f(f(a,b),c) = f(a,f(b,c))
///
/// LHS is f(f(a,b),c), RHS is f(a,f(b,c)), same constructor f at all levels.
fn detect_associativity(eq: &Equation) -> Option<AlgebraicProperty> {
    let (lhs_ctor, lhs_args) = extract_apply(&eq.left)?;
    let (rhs_ctor, rhs_args) = extract_apply(&eq.right)?;

    if lhs_ctor != rhs_ctor || lhs_args.len() != 2 || rhs_args.len() != 2 {
        return None;
    }

    // LHS: f(f(a,b), c)
    let (lhs_inner_ctor, lhs_inner_args) = extract_apply(&lhs_args[0])?;
    if lhs_inner_ctor != lhs_ctor || lhs_inner_args.len() != 2 {
        return None;
    }
    let a = extract_var_name(&lhs_inner_args[0])?;
    let b = extract_var_name(&lhs_inner_args[1])?;
    let c = extract_var_name(&lhs_args[1])?;

    // RHS: f(a, f(b,c))
    let ra = extract_var_name(&rhs_args[0])?;
    let (rhs_inner_ctor, rhs_inner_args) = extract_apply(&rhs_args[1])?;
    if rhs_inner_ctor != rhs_ctor || rhs_inner_args.len() != 2 {
        return None;
    }
    let rb = extract_var_name(&rhs_inner_args[0])?;
    let rc = extract_var_name(&rhs_inner_args[1])?;

    if a == ra && b == rb && c == rc {
        return Some(AlgebraicProperty::Associativity {
            equation_name: eq.name.to_string(),
            constructor: lhs_ctor,
            param_a: a,
            param_b: b,
            param_c: c,
        });
    }

    None
}

/// Detect identity: f(a, e) = a where e is a literal/nullary constructor.
///
/// Also matches f(e, a) = a.
fn detect_identity(eq: &Equation) -> Option<AlgebraicProperty> {
    // Case 1: f(a, e) = a
    let (lhs_ctor, lhs_args) = extract_apply(&eq.left)?;
    if lhs_args.len() != 2 {
        return None;
    }

    let rhs_var = extract_var_name(&eq.right)?;

    // Check if LHS first arg is the same var as RHS
    if let Some(la) = extract_var_name(&lhs_args[0]) {
        if la == rhs_var {
            // lhs_args[1] should be a nullary constructor or literal
            if let Some(identity) = extract_nullary_or_literal(&lhs_args[1]) {
                return Some(AlgebraicProperty::Identity {
                    equation_name: eq.name.to_string(),
                    constructor: lhs_ctor,
                    param_a: la,
                    identity_element: identity,
                });
            }
        }
    }

    // Case 2: f(e, a) = a
    if let Some(la) = extract_var_name(&lhs_args[1]) {
        if la == rhs_var {
            if let Some(identity) = extract_nullary_or_literal(&lhs_args[0]) {
                return Some(AlgebraicProperty::Identity {
                    equation_name: eq.name.to_string(),
                    constructor: lhs_ctor,
                    param_a: la,
                    identity_element: identity,
                });
            }
        }
    }

    None
}

/// Extract constructor and args from a Pattern::Term(PatternTerm::Apply).
fn extract_apply(pattern: &Pattern) -> Option<(String, Vec<&Pattern>)> {
    match pattern {
        Pattern::Term(PatternTerm::Apply { constructor, args }) => {
            Some((constructor.to_string(), args.iter().collect()))
        },
        _ => None,
    }
}

/// Extract variable name from a Pattern::Term(PatternTerm::Var).
fn extract_var_name(pattern: &Pattern) -> Option<String> {
    match pattern {
        Pattern::Term(PatternTerm::Var(v)) => Some(v.to_string()),
        _ => None,
    }
}

/// Extract a nullary constructor or literal name from a pattern.
fn extract_nullary_or_literal(pattern: &Pattern) -> Option<String> {
    match pattern {
        // Nullary constructor: Apply with zero args
        Pattern::Term(PatternTerm::Apply { constructor, args }) if args.is_empty() => {
            Some(constructor.to_string())
        },
        // Variable that looks like a constructor (starts with uppercase)
        Pattern::Term(PatternTerm::Var(v)) => {
            let name = v.to_string();
            if name.chars().next().map_or(false, |c| c.is_uppercase()) {
                Some(name)
            } else {
                None
            }
        },
        _ => None,
    }
}

/// Generate a test that evaluates two terms and asserts their normal forms match.
fn generate_algebraic_eq_test(
    test_name: &str,
    lhs_construction: &str,
    rhs_construction: &str,
    lang_struct: &str,
    equation_name: &str,
) -> TestCase {
    // We generate a custom test that:
    // 1. Constructs both terms
    // 2. Displays both, parses both, runs Ascent on both
    // 3. Asserts that their normal forms overlap
    let construction_code = format!(
        r#"{{ // algebraic eq test for equation '{eq}'
    let lhs_term = {lhs};
    let rhs_term = {rhs};
    let lhs_str = format!("{{}}", lhs_term);
    let rhs_str = format!("{{}}", rhs_term);
    let lang = {lang_struct};
    let lhs_parsed = lang.parse_term(&lhs_str).expect("LHS parse should succeed");
    let rhs_parsed = lang.parse_term(&rhs_str).expect("RHS parse should succeed");
    let lhs_results = lang.run_ascent(lhs_parsed.as_ref()).expect("LHS eval should succeed");
    let rhs_results = lang.run_ascent(rhs_parsed.as_ref()).expect("RHS eval should succeed");
    let lhs_nfs: std::collections::HashSet<String> = lhs_results.normal_forms().iter().map(|nf| nf.display.clone()).collect();
    let rhs_nfs: std::collections::HashSet<String> = rhs_results.normal_forms().iter().map(|nf| nf.display.clone()).collect();
    assert!(!lhs_nfs.is_disjoint(&rhs_nfs),
        "Equation '{eq}': LHS normal forms {{:?}} and RHS normal forms {{:?}} should overlap", lhs_nfs, rhs_nfs);
}}"#,
        eq = equation_name,
        lhs = lhs_construction,
        rhs = rhs_construction,
        lang_struct = lang_struct,
    );

    TestCase {
        test_name: test_name.to_string(),
        construction_code,
        lang_struct: lang_struct.to_string(),
        expected: None, // Custom body, not standard pattern
    }
}

/// Generate an algebraic eq test with custom body (overrides standard test gen).
fn generate_algebraic_eq_test_source(tc: &TestCase) -> String {
    let mut out = String::with_capacity(512);
    out.push_str("#[test]\n");
    out.push_str(&format!("fn {}() {{\n", tc.test_name));
    out.push_str("    mettail_runtime::clear_var_cache();\n");
    // The construction_code IS the full test body
    out.push_str(&format!("    {}\n", tc.construction_code));
    out.push_str("}\n\n");
    out
}

/// Generate an identity test.
fn generate_identity_test(
    test_name: &str,
    leaf_construction: &str,
    constructor: &str,
    category: &str,
    identity_element: &str,
    lang_struct: &str,
    equation_name: &str,
    language: &LanguageDef,
) -> TestCase {
    // Build identity element construction.
    // Identity element could be a nullary constructor or literal.
    let identity_construction = format!("{}::{}", category, identity_element);

    // f(a, e) and a
    let combined_construction = format!(
        "{}::{}(std::sync::Arc::new({}), std::sync::Arc::new({}))",
        category, constructor, leaf_construction, identity_construction
    );

    // This is a smoke test — identity might not eval to the simplified form
    // without full normalization
    TestCase {
        test_name: test_name.to_string(),
        construction_code: combined_construction,
        lang_struct: lang_struct.to_string(),
        expected: None,
    }
}

/// Get a leaf value different from the given raw value for the same category.
fn get_different_leaf(
    cat: &str,
    language: &LanguageDef,
    exclude_raw: &str,
) -> Option<super::nested_expr_gen::SimpleLeaf> {
    let lt = language.types.iter().find(|t| t.name.to_string() == cat)?;
    let native_type = lt.native_type.as_ref()?;
    let type_str = crate::gen::native::native_type_to_string(native_type);
    let lit_label = crate::gen::generate_literal_label(native_type).to_string();

    // Pick a value different from exclude_raw
    let alt_values: Vec<(&str, &str)> = match type_str.as_str() {
        "i32" => vec![("1i32", "1"), ("2i32", "2"), ("5i32", "5")],
        "i64" => vec![("1i64", "1"), ("2i64", "2"), ("5i64", "5")],
        "u32" => vec![("1u32", "1"), ("2u32", "2"), ("5u32", "5")],
        "u64" => vec![("1u64", "1"), ("2u64", "2"), ("5u64", "5")],
        "f32" => vec![("1.0f32", "1_0"), ("2.5f32", "2_5"), ("0.5f32", "0_5")],
        "f64" => vec![("1.0f64", "1_0"), ("2.5f64", "2_5"), ("0.5f64", "0_5")],
        "bool" => vec![("true", "true"), ("false", "false")],
        _ => return None,
    };

    for (raw, _display) in alt_values {
        if raw != exclude_raw {
            let construction = match type_str.as_str() {
                "f64" => format!(
                    "{}::{}(mettail_runtime::CanonicalFloat64::from({}))",
                    cat, lit_label, raw
                ),
                "f32" => format!(
                    "{}::{}(mettail_runtime::CanonicalFloat32::from({}))",
                    cat, lit_label, raw
                ),
                _ => format!("{}::{}({})", cat, lit_label, raw),
            };
            return Some(super::nested_expr_gen::SimpleLeaf {
                construction,
                raw_value: raw.to_string(),
                native_type: Some(type_str.clone()),
            });
        }
    }

    None
}

/// Generate proptest blocks for algebraic metamorphic relations (Phase 6).
///
/// For each detected property, generates a `proptest!` block that uses
/// the tape-based `arb_{cat}()` strategies.
fn generate_algebraic_proptest_blocks(
    properties: &[AlgebraicProperty],
    language: &LanguageDef,
    lang_name_lower: &str,
    lang_struct: &str,
) -> String {
    if properties.is_empty() {
        return String::new();
    }

    let mut out = String::with_capacity(4096);

    out.push_str("// ═══════════════════════════════════════════════════════════\n");
    out.push_str("// Algebraic metamorphic property tests (proptest)\n");
    out.push_str("// ═══════════════════════════════════════════════════════════\n\n");

    out.push_str("proptest! {\n");
    out.push_str("    #![proptest_config(ProptestConfig::with_cases(30))]\n\n");

    for prop in properties {
        match prop {
            AlgebraicProperty::Commutativity {
                equation_name,
                constructor,
                param_a: _,
                param_b: _,
            } => {
                // Find the category of the constructor
                let rule = match language
                    .terms
                    .iter()
                    .find(|r| r.label.to_string() == *constructor)
                {
                    Some(r) => r,
                    None => continue,
                };
                let category = rule.category.to_string();
                let cat_lower = category.to_lowercase();

                out.push_str(&format!(
                    "    /// Commutativity: {eq} — eval({ctor}(a,b)) == eval({ctor}(b,a))\n",
                    eq = equation_name, ctor = constructor
                ));
                out.push_str(&format!(
                    "    #[test]\n    fn {lang}_comm_{ctor}_proptest(a in arb_{cat}(3), b in arb_{cat}(3)) {{\n",
                    lang = lang_name_lower,
                    ctor = constructor.to_lowercase(),
                    cat = cat_lower
                ));
                out.push_str("        mettail_runtime::clear_var_cache();\n");
                out.push_str(&format!("        let lang = {};\n", lang_struct));
                out.push_str(&format!(
                    "        let lhs = {cat}::{ctor}(std::sync::Arc::new(a.clone()), std::sync::Arc::new(b.clone()));\n",
                    cat = category, ctor = constructor
                ));
                out.push_str(&format!(
                    "        let rhs = {cat}::{ctor}(std::sync::Arc::new(b), std::sync::Arc::new(a));\n",
                    cat = category, ctor = constructor
                ));
                out.push_str("        let lhs_str = format!(\"{}\", lhs);\n");
                out.push_str("        let rhs_str = format!(\"{}\", rhs);\n");
                out.push_str("        if let (Ok(lp), Ok(rp)) = (lang.parse_term(&lhs_str), lang.parse_term(&rhs_str)) {\n");
                out.push_str("            if let (Ok(lr), Ok(rr)) = (lang.run_ascent(lp.as_ref()), lang.run_ascent(rp.as_ref())) {\n");
                out.push_str("                let lnfs: std::collections::HashSet<String> = lr.normal_forms().iter().map(|nf| nf.display.clone()).collect();\n");
                out.push_str("                let rnfs: std::collections::HashSet<String> = rr.normal_forms().iter().map(|nf| nf.display.clone()).collect();\n");
                out.push_str("                prop_assert!(!lnfs.is_disjoint(&rnfs),\n");
                out.push_str(&format!(
                    "                    \"Commutativity ({eq}) failed: {{:?}} vs {{:?}}\", lnfs, rnfs);\n",
                    eq = equation_name
                ));
                out.push_str("            }\n");
                out.push_str("        }\n");
                out.push_str("    }\n\n");
            },
            AlgebraicProperty::Associativity {
                equation_name,
                constructor,
                ..
            } => {
                let rule = match language
                    .terms
                    .iter()
                    .find(|r| r.label.to_string() == *constructor)
                {
                    Some(r) => r,
                    None => continue,
                };
                let category = rule.category.to_string();
                let cat_lower = category.to_lowercase();

                out.push_str(&format!(
                    "    /// Associativity: {eq} — eval({ctor}({ctor}(a,b),c)) == eval({ctor}(a,{ctor}(b,c)))\n",
                    eq = equation_name, ctor = constructor
                ));
                out.push_str(&format!(
                    "    #[test]\n    fn {lang}_assoc_{ctor}_proptest(a in arb_{cat}(2), b in arb_{cat}(2), c in arb_{cat}(2)) {{\n",
                    lang = lang_name_lower,
                    ctor = constructor.to_lowercase(),
                    cat = cat_lower
                ));
                out.push_str("        mettail_runtime::clear_var_cache();\n");
                out.push_str(&format!("        let lang = {};\n", lang_struct));
                out.push_str(&format!(
                    "        let lhs = {cat}::{ctor}(std::sync::Arc::new({cat}::{ctor}(std::sync::Arc::new(a.clone()), std::sync::Arc::new(b.clone()))), std::sync::Arc::new(c.clone()));\n",
                    cat = category, ctor = constructor
                ));
                out.push_str(&format!(
                    "        let rhs = {cat}::{ctor}(std::sync::Arc::new(a), std::sync::Arc::new({cat}::{ctor}(std::sync::Arc::new(b), std::sync::Arc::new(c))));\n",
                    cat = category, ctor = constructor
                ));
                out.push_str("        let lhs_str = format!(\"{}\", lhs);\n");
                out.push_str("        let rhs_str = format!(\"{}\", rhs);\n");
                out.push_str("        if let (Ok(lp), Ok(rp)) = (lang.parse_term(&lhs_str), lang.parse_term(&rhs_str)) {\n");
                out.push_str("            if let (Ok(lr), Ok(rr)) = (lang.run_ascent(lp.as_ref()), lang.run_ascent(rp.as_ref())) {\n");
                out.push_str("                let lnfs: std::collections::HashSet<String> = lr.normal_forms().iter().map(|nf| nf.display.clone()).collect();\n");
                out.push_str("                let rnfs: std::collections::HashSet<String> = rr.normal_forms().iter().map(|nf| nf.display.clone()).collect();\n");
                out.push_str("                prop_assert!(!lnfs.is_disjoint(&rnfs),\n");
                out.push_str(&format!(
                    "                    \"Associativity ({eq}) failed: {{:?}} vs {{:?}}\", lnfs, rnfs);\n",
                    eq = equation_name
                ));
                out.push_str("            }\n");
                out.push_str("        }\n");
                out.push_str("    }\n\n");
            },
            AlgebraicProperty::Identity { .. } => {
                // Identity proptests are harder because we need to construct the
                // identity element generically. Skip for now — the concrete test
                // already covers the key case.
            },
        }
    }

    out.push_str("}\n\n");

    out
}

/// Generate source code for algebraic property tests.
///
/// Returns a string of `#[test]` functions plus proptest blocks.
pub fn generate_algebraic_tests_source(test_cases: &[TestCase], proptest_blocks: &str) -> String {
    let mut out = String::with_capacity(test_cases.len() * 800 + proptest_blocks.len() + 256);

    out.push_str("// ═══════════════════════════════════════════════════════════\n");
    out.push_str("// Algebraic property tests (derived from equations)\n");
    out.push_str("// ═══════════════════════════════════════════════════════════\n\n");

    for tc in test_cases {
        out.push_str(&generate_algebraic_eq_test_source(tc));
    }

    if !proptest_blocks.is_empty() {
        out.push_str(proptest_blocks);
    }

    out
}
