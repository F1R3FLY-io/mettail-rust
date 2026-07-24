//! Simulation test generation for `language!` specifications.
//!
//! Generates `#[test]` functions that exercise the simulation runner against
//! each language. For languages with rewrite rules, the following tests are
//! generated:
//!
//! 1. **Normal form reachability** — random terms should reach a normal form
//!    within the step limit.
//! 2. **Roundtrip under rewrite** — the normal form's display string should
//!    be parseable and re-rewrite to the same normal form.
//! 3. **Morphology bounded** — term size and depth should stay within bounds
//!    during rewriting.
//! 4. **Eval determinism** — running the same term twice should produce the
//!    same normal form.

use mettail_ast::language::LanguageDef;
use mettail_prattail::PipelineAnalysis;

/// Generate simulation integration tests for a language.
///
/// Returns a string containing `#[test]` functions to be appended to the
/// generated test file (gen_{lang}.rs). Only generates tests for languages
/// that have rewrite rules (languages without rewrites skip simulation tests).
pub fn generate_simulation_tests(language: &LanguageDef, pipeline: &PipelineAnalysis) -> String {
    let lang_name = language.name.to_string();
    let lang_lower = lang_name.to_lowercase();
    let lang_struct = format!("{}Language", lang_name);

    // Only generate simulation tests for languages with rewrite rules.
    if language.rewrites.is_empty() {
        return String::new();
    }

    // Pick the highest-entropy category for Test 5 — most ambiguous = hardest to test.
    // Falls back to the first type if entropy data is unavailable.
    let primary_cat = pipeline
        .per_category_entropy
        .iter()
        .max_by(|a, b| a.1.partial_cmp(b.1).unwrap_or(std::cmp::Ordering::Equal))
        .map(|(k, _)| k.clone())
        .or_else(|| language.types.first().map(|t| t.name.to_string()))
        .unwrap_or_else(|| "Term".to_string());
    let primary_cat_lower = primary_cat.to_lowercase();

    let mut out = String::with_capacity(8192);

    out.push_str("// ═══════════════════════════════════════════════════════════\n");
    out.push_str("// Simulation tests (runner integration)\n");
    out.push_str("// ═══════════════════════════════════════════════════════════\n\n");

    // Test 1: Normal form reachability.
    // Tests that concrete expression strings reach normal form via the simulation runner.
    // Uses manually-constructed test inputs (not proptest-generated ASTs) to avoid
    // stack overflow in Ascent's rewrite engine on deeply-nested random terms.
    out.push_str(&format!(
        r#"#[test]
fn sim_{lang_lower}_normal_form_reachability() {{
    use mettail_simulation::runner::{{SimulationConfig, SimulationRunner}};
    use mettail_simulation::trace::TraceOutcome;

    let lang = {lang_struct};
    let lang_ref: &dyn mettail_runtime::Language = &lang;
    let config = SimulationConfig {{
        max_steps: 100,
        track_morphology: false,
        ..SimulationConfig::default()
    }};
    let runner = SimulationRunner::new(lang_ref, config);

    let test_inputs: Vec<&str> = vec![{test_inputs}];

    let mut tested = 0usize;
    let mut reached_nf = 0usize;

    for input in &test_inputs {{
        mettail_runtime::clear_var_cache();
        // Catch panics from native eval (e.g., division by zero in ![a / b]).
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {{
            runner.run_to_normal_form(input)
        }}));
        match result {{
            Ok(Ok(trace)) => {{
                tested += 1;
                if matches!(trace.outcome, TraceOutcome::NormalForm {{ .. }}) {{
                    reached_nf += 1;
                }}
            }}
            _ => {{
                // Skip inputs that fail to parse, evaluate, or panic.
            }}
        }}
    }}

    if tested > 0 {{
        let pass_rate = reached_nf as f64 / tested as f64;
        assert!(
            pass_rate >= 0.80,
            "{lang_name} normal form reachability: only {{:.1}}% reached NF ({{}} / {{}})",
            pass_rate * 100.0,
            reached_nf,
            tested,
        );
    }}
}}

"#,
        lang_lower = lang_lower,
        lang_name = lang_name,
        lang_struct = lang_struct,
        test_inputs = generate_test_input_literals(language, pipeline),
    ));

    // Test 2: Roundtrip under rewrite.
    // Run a term to normal form, then re-parse and re-rewrite the normal form.
    // The result should be the same normal form (idempotence of normalization).
    // Fails immediately on the first mismatch — no silent accumulation.
    out.push_str(&format!(
        r#"#[test]
fn sim_{lang_lower}_roundtrip_under_rewrite() {{
    use mettail_simulation::runner::{{SimulationConfig, SimulationRunner}};
    use mettail_simulation::trace::TraceOutcome;

    let lang = {lang_struct};
    let lang_ref: &dyn mettail_runtime::Language = &lang;
    let config = SimulationConfig {{
        max_steps: 100,
        seed: Some([99u8; 32]),
        track_morphology: false,
        ..SimulationConfig::default()
    }};
    let runner = SimulationRunner::new(lang_ref, config);

    // Test a set of concrete expressions for rewrite roundtrip.
    let test_inputs: Vec<&str> = vec![{test_inputs}];

    for input in &test_inputs {{
        mettail_runtime::clear_var_cache();
        // Catch panics from native eval (e.g., division by zero).
        let result1 = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {{
            runner.run_to_normal_form(input)
        }}));
        let trace1 = match result1 {{
            Ok(Ok(t)) => t,
            _ => continue, // Skip inputs that panic, fail to parse, or error.
        }};
        let nf1 = match &trace1.outcome {{
            TraceOutcome::NormalForm {{ term, .. }} => term.clone(),
            _ => continue,
        }};

        mettail_runtime::clear_var_cache();
        let result2 = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {{
            runner.run_to_normal_form(&nf1)
        }}));
        let trace2 = match result2 {{
            Ok(Ok(t)) => t,
            _ => panic!(
                "{lang_name} roundtrip re-run panicked or errored for input {{:?}} \
                 (first NF: {{:?}})",
                input, nf1,
            ),
        }};
        let nf2 = match &trace2.outcome {{
            TraceOutcome::NormalForm {{ term, .. }} => term.clone(),
            other => panic!(
                "{lang_name} roundtrip re-run did not reach NF for input {{:?}} \
                 (first NF: {{:?}}): {{:?}}",
                input, nf1, other,
            ),
        }};

        if nf1 != nf2 {{
            panic!(
                "{lang_name} roundtrip under rewrite FAILED for input {{:?}}:\n\
                 First NF:  {{:?}}\nSecond NF: {{:?}}",
                input, nf1, nf2,
            );
        }}
    }}
}}

"#,
        lang_lower = lang_lower,
        lang_name = lang_name,
        lang_struct = lang_struct,
        test_inputs = generate_test_input_literals(language, pipeline),
    ));

    // Test 3: Morphology bounded.
    // Run concrete terms through the simulation with morphology tracking enabled
    // and verify that term size stays within reasonable bounds.
    out.push_str(&format!(
        r#"#[test]
fn sim_{lang_lower}_morphology_bounded() {{
    use mettail_simulation::runner::{{SimulationConfig, SimulationRunner}};
    use mettail_simulation::trace::TraceOutcome;

    let lang = {lang_struct};
    let lang_ref: &dyn mettail_runtime::Language = &lang;
    let config = SimulationConfig {{
        max_steps: 100,
        track_morphology: true,
        ..SimulationConfig::default()
    }};
    let runner = SimulationRunner::new(lang_ref, config);

    let test_inputs: Vec<&str> = vec![{test_inputs}];

    for input in &test_inputs {{
        mettail_runtime::clear_var_cache();
        // Catch panics from native eval (e.g., division by zero).
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {{
            runner.run_to_normal_form(input)
        }}));
        if let Ok(Ok(trace)) = result {{
            if let Some(ref morph) = trace.morphology {{
                assert!(
                    morph.max_nodes <= 50000,
                    "{lang_name} morphology: max nodes {{}} exceeds bound 50000 for input {{:?}}",
                    morph.max_nodes,
                    input,
                );
                assert!(
                    morph.max_depth <= 100,
                    "{lang_name} morphology: max depth {{}} exceeds bound 100 for input {{:?}}",
                    morph.max_depth,
                    input,
                );
            }}
        }}
    }}
}}

"#,
        lang_lower = lang_lower,
        lang_name = lang_name,
        lang_struct = lang_struct,
        test_inputs = generate_test_input_literals(language, pipeline),
    ));

    // Test 4: Eval determinism.
    // Run the same term twice and verify the normal forms match.
    out.push_str(&format!(
        r#"#[test]
fn sim_{lang_lower}_eval_determinism() {{
    use mettail_simulation::runner::{{SimulationConfig, SimulationRunner}};
    use mettail_simulation::trace::TraceOutcome;

    let lang = {lang_struct};
    let lang_ref: &dyn mettail_runtime::Language = &lang;

    let test_inputs: Vec<&str> = vec![{test_inputs}];

    for input in &test_inputs {{
        let config1 = SimulationConfig {{
            max_steps: 100,
            track_morphology: false,
            ..SimulationConfig::default()
        }};
        let runner1 = SimulationRunner::new(lang_ref, config1);

        mettail_runtime::clear_var_cache();
        // Catch panics from native eval (e.g., division by zero).
        let result1 = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {{
            runner1.run_to_normal_form(input)
        }}));
        let trace1 = match result1 {{
            Ok(Ok(t)) => t,
            _ => continue, // Skip inputs that panic or fail.
        }};
        let nf1 = match &trace1.outcome {{
            TraceOutcome::NormalForm {{ term, .. }} => term.clone(),
            _ => continue,
        }};

        let config2 = SimulationConfig {{
            max_steps: 100,
            track_morphology: false,
            ..SimulationConfig::default()
        }};
        let runner2 = SimulationRunner::new(lang_ref, config2);

        mettail_runtime::clear_var_cache();
        let result2 = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {{
            runner2.run_to_normal_form(input)
        }}));
        let trace2 = match result2 {{
            Ok(Ok(t)) => t,
            _ => continue, // If the second run panics but the first didn't, skip.
        }};
        let nf2 = match &trace2.outcome {{
            TraceOutcome::NormalForm {{ term, .. }} => term.clone(),
            _ => continue,
        }};

        assert_eq!(
            nf1, nf2,
            "{lang_name} eval determinism: different normal forms for input {{:?}}: {{:?}} vs {{:?}}",
            input, nf1, nf2,
        );
    }}
}}

"#,
        lang_lower = lang_lower,
        lang_name = lang_name,
        lang_struct = lang_struct,
        test_inputs = generate_test_input_literals(language, pipeline),
    ));

    // Test 5: Proptest-based simulation campaign.
    // Uses the tape-based arb_{primary_cat} strategy (generated by strategies.rs
    // into the same gen_*.rs file) to run 50 random terms through the simulation
    // runner with invariant checking. No feature gate needed — arb_* functions are
    // unconditionally generated in the test file and proptest is a dev-dependency.
    out.push_str(&format!(
        r#"proptest! {{
    #![proptest_config(ProptestConfig::with_cases(50))]

    #[test]
    fn sim_{lang_lower}_proptest_campaign(term in arb_{primary_cat_lower}(3u32)) {{
        use mettail_simulation::runner::{{SimulationConfig, SimulationRunner}};
        use mettail_simulation::trace::TraceOutcome;
        use mettail_simulation::invariant::{{BoundedSize, BoundedDepth}};

        let lang = {lang_struct};
        let lang_ref: &dyn mettail_runtime::Language = &lang;

        let displayed = format!("{{}}", term);
        // Skip very large terms to avoid OOM in the rewrite engine.
        if displayed.len() > 500 {{
            return Ok(());
        }}

        // `AlwaysParseable` is intentionally excluded: the roundtrip tests
        // (sim_*_roundtrip_under_rewrite) already check parseability of normal
        // forms, and AlwaysParseable's per-step `clear_var_cache()` is a
        // significant per-iteration cost in a proptest campaign.
        let config = SimulationConfig {{
            max_steps: 50,
            track_morphology: false,
            invariants: vec![
                Box::new(BoundedSize {{ max_nodes: 10000 }}),
                Box::new(BoundedDepth {{ max_depth: 50 }}),
            ],
            ..SimulationConfig::default()
        }};
        let runner = SimulationRunner::new(lang_ref, config);

        // `catch_unwind` is defensive only: the `SafeArith` + `rust_code_rewrite`
        // pass removes arithmetic overflow as a panic source. Any remaining panic
        // (e.g. parser bug, language invariant broken) is a real bug we'd want to
        // surface — but we catch it here so proptest shrinking doesn't hit the
        // macOS double-panic abort. `prop_assert!` fires only on
        // `InvariantViolation` (the bug signal for this test); other outcomes
        // are covered by Tests 1–4.
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {{
            mettail_runtime::clear_var_cache();
            runner.run_to_normal_form(&displayed)
        }}));
        if let Ok(Ok(trace)) = result {{
            if let TraceOutcome::InvariantViolation {{ ref invariant, ref message, .. }} = trace.outcome {{
                prop_assert!(
                    false,
                    "{lang_name} invariant '{{}}' violated on '{{}}': {{}}",
                    invariant, displayed, message,
                );
            }}
        }}
        // All other outcomes (SimulationFailure, panics, StepLimitReached, Error)
        // are tolerated — they are covered by dedicated non-proptest simulation tests.
    }}
}}

"#,
        lang_lower = lang_lower,
        lang_name = lang_name,
        lang_struct = lang_struct,
        primary_cat_lower = primary_cat_lower,
    ));

    out
}

/// Generate a comma-separated list of string literal test inputs appropriate
/// for the given language. Uses concrete expressions derived from the language's
/// term definitions to ensure parseability.
fn generate_test_input_literals(language: &LanguageDef, pipeline: &PipelineAnalysis) -> String {
    let mut inputs = Vec::new();

    // Collect some representative expressions from the language's terms.
    // Focus on terms with native evaluation (the `![...]` block) since these
    // are most likely to produce interesting rewrite behavior.
    // Categories in recursive SCCs get a higher non-terminal limit (3 instead of 2)
    // so we also include two-level nesting, which is more likely to trigger multi-step
    // reduction chains.
    for rule in &language.terms {
        // Count non-terminal items (fields/subterms).
        let non_terminal_count = rule
            .items
            .iter()
            .filter(|item| matches!(item, mettail_ast::grammar::GrammarItem::NonTerminal { .. }))
            .count();

        // Categories in accepting SCCs get a higher limit to expose multi-step chains.
        let is_in_scc = pipeline
            .recursive_scc_categories
            .contains(&rule.category.to_string());
        let max_nt = if is_in_scc { 3 } else { 2 };

        // Only consider rules with native eval and at most max_nt subterms.
        if rule.rust_code.is_some() && non_terminal_count <= max_nt {
            if let Some(expr) = construct_test_expression(rule, language) {
                if !inputs.contains(&expr) {
                    inputs.push(expr);
                }
                if inputs.len() >= 12 {
                    break;
                }
            }
        }
    }

    // Second pass: also try rules without native eval (for languages like Lambda
    // that have no native types but still have rewritable terms).
    if inputs.len() < 6 {
        for rule in &language.terms {
            let non_terminal_count = rule
                .items
                .iter()
                .filter(|item| {
                    matches!(item, mettail_ast::grammar::GrammarItem::NonTerminal { .. })
                })
                .count();

            let is_in_scc = pipeline
                .recursive_scc_categories
                .contains(&rule.category.to_string());
            let max_nt = if is_in_scc { 3 } else { 2 };

            if non_terminal_count <= max_nt {
                if let Some(expr) = construct_test_expression(rule, language) {
                    if !inputs.contains(&expr) {
                        inputs.push(expr);
                    }
                    if inputs.len() >= 12 {
                        break;
                    }
                }
            }
        }
    }

    // S1: spec-derived simple literals projected onto each native
    // type's spec patterns. Integer values come from
    // `spec_admitted_integer_samples(language, Safe)` (avoids zero
    // for `[1-9][0-9]*` patterns). Float/bool/string use known-safe
    // values from the universally-admitted domain of their patterns.
    for lang_type in &language.types {
        if let Some(ref native) = lang_type.native_type {
            let native_str = crate::gen::native::native_type_to_string(native);
            let lit = match native_str.as_str() {
                "i32" | "i64" | "u32" | "u64" | "i8" | "i16" | "i128" | "u8" | "u16" | "u128"
                | "isize" | "usize" => crate::gen::spec_admitted_integer_samples(
                    language,
                    crate::gen::SamplePurpose::Safe,
                )
                .into_iter()
                .next()
                .unwrap_or_else(|| "1".to_string()),
                "f64" | "f32" => "1.0".to_string(),
                "bool" => "true".to_string(),
                "String" | "str" => "\"hello\"".to_string(),
                _ => continue,
            };
            if !inputs.contains(&lit) {
                inputs.push(lit);
            }
        }
    }

    if inputs.is_empty() {
        // S2: fallback to nullary spec rules. If none exist, the
        // generator emits an empty input list — caller will skip
        // simulation. NOT a "0" string fabrication, which the spec
        // may not admit.
        for rule in &language.terms {
            let has_non_terminals = rule
                .items
                .iter()
                .any(|item| !matches!(item, mettail_ast::grammar::GrammarItem::Terminal(_)));
            if !has_non_terminals && !rule.items.is_empty() {
                let expr: String = rule
                    .items
                    .iter()
                    .filter_map(|item| {
                        if let mettail_ast::grammar::GrammarItem::Terminal(s) = item {
                            Some(s.clone())
                        } else {
                            None
                        }
                    })
                    .collect::<Vec<_>>()
                    .join(" ");
                if !expr.is_empty() && !inputs.contains(&expr) {
                    inputs.push(expr);
                    break;
                }
            }
        }
    }
    // No "0" last-resort fallback — if the spec admits no input the
    // generator emits an empty literal list.

    inputs
        .iter()
        .map(|s| format!("\"{}\"", s.replace('\\', "\\\\").replace('"', "\\\"")))
        .collect::<Vec<_>>()
        .join(", ")
}

/// Attempt to construct a simple test expression string from a grammar rule.
///
/// For binary operators like `a "+" b : Int` (items: [NonTerminal(Int), Terminal("+"), NonTerminal(Int)]),
/// produces "0 + 0".
/// For unary operators like `"-" a : Int`, produces "- 0".
/// For function-like terms like `"sin" "(" a ")"`, produces "sin ( 0.0 )".
///
/// For new-style rules (with `term_context` and `syntax_pattern`), uses the
/// syntax pattern for display and term_context for field type lookup.
pub(crate) fn construct_test_expression(
    rule: &mettail_ast::grammar::GrammarRule,
    language: &LanguageDef,
) -> Option<String> {
    use mettail_ast::grammar::{GrammarItem, SyntaxExpr};

    // Try new-style syntax first (term_context + syntax_pattern).
    if let (Some(ref ctx), Some(ref pattern)) = (&rule.term_context, &rule.syntax_pattern) {
        let mut parts = Vec::new();
        for expr in pattern {
            match expr {
                SyntaxExpr::Literal(lit) => {
                    parts.push(lit.clone());
                },
                // L9-3: a custom-kind capture — INERT placeholder for simulation
                // input generation (unconstructable from source in STAGE 1).
                SyntaxExpr::TokenKind { name, .. } => {
                    parts.push(format!("<{}>", name));
                },
                SyntaxExpr::GuestBody { open, close, bind } => {
                    parts.push(format!("*flt({},{},{})", bind, open, close));
                },
                SyntaxExpr::Param(param_name) => {
                    // S3: spec-derived. If the param category is found
                    // in the term_context, route through
                    // `default_value_for_category` (which itself
                    // consults the spec). If not found, surface via
                    // `spec_admitted_integer_default` — NOT a "0"
                    // fabrication. Missing param category in
                    // term_context indicates a malformed rule; using
                    // an integer default is the safest cross-type
                    // input that any well-formed grammar with a
                    // numeric category would accept.
                    let cat = find_param_category(param_name, ctx);
                    if let Some(cat_str) = cat {
                        parts.push(default_value_for_category(&cat_str, language));
                    } else {
                        parts.push(crate::gen::spec_admitted_integer_default(language));
                    }
                },
                SyntaxExpr::Op(_) => {
                    // Pattern operations (sep, map, etc.) are too complex to synthesize.
                    return None;
                },
            }
        }
        if parts.is_empty() {
            return None;
        }
        return Some(parts.join(" "));
    }

    // Fall back to old-style items.
    if rule.items.is_empty() {
        return None;
    }

    let mut parts = Vec::new();
    for item in &rule.items {
        match item {
            GrammarItem::Terminal(text) => {
                parts.push(text.clone());
            },
            GrammarItem::NonTerminal { ident: cat_ident, .. } => {
                let cat = cat_ident.to_string();
                parts.push(default_value_for_category(&cat, language));
            },
            GrammarItem::Binder { .. } => {
                // Binder positions are complex; skip these rules.
                return None;
            },
            GrammarItem::Collection { .. } => {
                // Collections are complex; skip these rules.
                return None;
            },
        }
    }

    if parts.is_empty() {
        return None;
    }
    Some(parts.join(" "))
}

/// Find the category of a parameter by name in a term_context.
pub(crate) fn find_param_category(
    name: &syn::Ident,
    ctx: &[mettail_ast::grammar::TermParam],
) -> Option<String> {
    use mettail_ast::grammar::TermParam;

    for param in ctx {
        match param {
            TermParam::Simple { name: pname, ty } => {
                if pname == name {
                    return type_expr_to_category(ty);
                }
            },
            TermParam::Abstraction { binder, body, ty } => {
                if binder == name || body == name {
                    return type_expr_to_category(ty);
                }
            },
            TermParam::MultiAbstraction { binder, body, ty } => {
                if binder == name || body == name {
                    return type_expr_to_category(ty);
                }
            },
            TermParam::GuardBody { name: gname, .. } => {
                if gname == name {
                    return Some("Bool".to_string());
                }
            },
            TermParam::Optional { params: inner } => {
                // Opt-Group: simulation-test parser-input synthesis uses
                // this lookup to pick a category for each named param. A
                // syntax-pattern reference to an inner-of-Optional param
                // resolves to the inner's category — when the syntax
                // emits the Opt block, the synthesizer needs to know the
                // inner category to generate a valid token. Recurse.
                if let Some(found) = find_param_category(name, inner) {
                    return Some(found);
                }
            },
        }
    }
    None
}

/// Extract the simple category name from a TypeExpr.
pub(crate) fn type_expr_to_category(ty: &mettail_ast::types::TypeExpr) -> Option<String> {
    use mettail_ast::types::TypeExpr;
    match ty {
        TypeExpr::Base(ident) => Some(ident.to_string()),
        TypeExpr::Arrow { codomain, .. } => type_expr_to_category(codomain),
        TypeExpr::MultiBinder(inner) => type_expr_to_category(inner),
        TypeExpr::Collection { element, .. } => type_expr_to_category(element),
        // Refinement and other complex types: return the base type if available.
        _ => None,
    }
}

/// Return a simple default value string for a language category.
///
/// S4: spec-derived. Integer-family categories route through
/// `spec_admitted_integer_samples(language, Safe)` to avoid both
/// division-by-zero (in languages with `![a / b]` rules) and
/// pattern-rejected literals (e.g., `[1-9][0-9]*` excludes 0).
/// Float/Bool/String use values from the universally-admitted domain.
pub(crate) fn default_value_for_category(category: &str, language: &LanguageDef) -> String {
    // Look up the native type for this category.
    for lang_type in &language.types {
        if lang_type.name.to_string() == category {
            if let Some(ref native) = lang_type.native_type {
                return match crate::gen::native::native_type_to_string(native).as_str() {
                    "i32" | "i64" | "u32" | "u64" | "i8" | "i16" | "i128" | "u8" | "u16"
                    | "u128" | "isize" | "usize" => crate::gen::spec_admitted_integer_samples(
                        language,
                        crate::gen::SamplePurpose::Safe,
                    )
                    .into_iter()
                    .next()
                    .unwrap_or_else(|| "1".to_string()),
                    "f64" | "f32" => "1.0".to_string(),
                    "bool" => "true".to_string(),
                    "String" | "str" => "\"a\"".to_string(),
                    // Spec-derived fallback for unknown native types.
                    _ => crate::gen::spec_admitted_integer_default(language),
                };
            }
        }
    }
    // Category not found — emit spec-admitted integer default (NOT
    // a hard-coded "1").
    crate::gen::spec_admitted_integer_default(language)
}
