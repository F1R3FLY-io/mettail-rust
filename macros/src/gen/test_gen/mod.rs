//! Test file generation for `language!` specifications.
//!
//! This module generates `languages/tests/generated/{name}_tests.rs` files
//! containing `#[test]` and `proptest!` functions that exercise the language
//! specification. Generated tests cover:
//!
//! 1. **Unit tests** — one per constructor (roundtrip with concrete values)
//! 2. **Equation tests** — one per equation (symmetry via Ascent)
//! 3. **Rewrite tests** — one per rewrite rule (fires + result matches)
//! 4. **Property tests** — proptest per category (roundtrip, display idempotence, etc.)
//! 5. **Analytical tests** -- confluence, termination
//! 6. **User tests** — from `tests { }` block
//! 7. **Program tests** — application-level from `program { }` blocks
//! 8. **Dead-rule tests** — `#[ignore]` annotated

pub mod automaton_walk;
pub mod equation_tests;
pub mod operational_tests;
pub mod rewrite_tests;
pub mod strategies;
pub mod unit_tests;

pub mod analytical_tests;
pub mod program_tests;
pub mod user_tests;

pub mod simulation_binary;
pub mod simulation_tests;

// ─── W7 Stage 9 (plan v5.1) ─────────────────────────────────────────────────
// Six test_gen modules covering ambiguity-prone WPDS walker paths. Each
// emits baseline tests per language and is wired into the analytical split
// test binary below.

pub mod ambiguity_exposure;
pub mod binder_shadowing;
pub mod cross_cat_ambiguity;
pub mod pratt_bp_boundaries;
pub mod recovery_corruption;
// Stage 10.1 (2026-05-04): parity test generator deleted.
// Pre-Stage-10b parity tests compared `Cat::parse(input)` (trampoline) vs
// `parse_<Cat>_via_wpda(...)` (WPDS facade); both routes are now Walker-driven
// after Stage 10b's parse_preserving_vars rewrite. Tests became tautological.

use mettail_ast::language::LanguageDef;
use mettail_prattail::PipelineAnalysis;
use std::path::PathBuf;

/// Write generated test files for the language, split into multiple
/// test-binary files to bound rustc peak memory per compilation unit.
///
/// # Why split?
///
/// Prior to this split, each language's tests were emitted as a single
/// monolithic `gen_{lang}.rs` (24,000+ lines for Calculator). rustc held
/// the full AST, type info, and codegen IR for that entire file in one
/// process, peaking at 96 GB RSS on a 125 GB machine — unusable on any
/// standard developer laptop.
///
/// Splitting into per-section files gives each a bounded size:
/// cargo auto-discovers `tests/*.rs` as separate integration-test
/// binaries, compiled in parallel with per-process memory proportional
/// to the file. Each binary peaks at O(file size), so a 16 GB laptop
/// can compile them all in parallel without swap thrashing.
///
/// # File map
///
/// Each emitted file is a self-contained test binary with its own
/// imports. Cross-section dependencies are isolated:
/// - `gen_{lang}_unit.rs`        — per-constructor unit tests + language-level smoke + metadata
/// - `gen_{lang}_prop.rs`        — property tests (defines AnyTerm/TapeReader/build_*/arb_*) + simulation tests that use arb_*
/// - `gen_{lang}_rewrite.rs`     — equation + rewrite rule tests
/// - `gen_{lang}_op.rs`          — operational semantics eval tests (all phases, may be further split if still too large)
/// - `gen_{lang}_analytical.rs`  — analytical + user + program tests (small)
///
/// Stale `gen_{lang}.rs` (monolithic) is deleted on first run to avoid
/// duplicate #[test] symbols across old and new binaries.
pub fn write_test_file(language: &LanguageDef, pipeline: &PipelineAnalysis) {
    let lang_name = language.name.to_string();

    // Group H: WFST static verification — emit warnings at codegen time
    verify_display_parseability(language, pipeline);

    // Delete the stale monolithic file if it exists (pre-split artifact).
    delete_stale_monolithic_file(&lang_name);

    // Emit each section as a separate test-binary file.
    let unit_content = generate_unit_section(language, pipeline);
    write_test_section(&lang_name, "unit", &unit_content);

    let prop_content = generate_prop_section(language, pipeline);
    write_test_section(&lang_name, "prop", &prop_content);

    if !language.equations.is_empty() || !language.rewrites.is_empty() {
        let rewrite_content = generate_rewrite_section(language, pipeline);
        write_test_section(&lang_name, "rewrite", &rewrite_content);
    }

    let op_content = generate_op_section(language, pipeline);
    if !op_content.is_empty() {
        write_test_section(&lang_name, "op", &op_content);
    }

    let analytical_content = generate_analytical_section(language, pipeline);
    if !analytical_content.is_empty() {
        write_test_section(&lang_name, "analytical", &analytical_content);
    }

    // Stage 10.1 (2026-05-04): parity-section emission deleted alongside
    // `parity` module. The dual-codegen comparison was tautological after
    // Stage 10b's parse_preserving_vars rewrite (both routes Walker-driven).
}

/// Emit a standard test-file header (imports and allow directives)
/// shared by every per-section file.
fn emit_test_file_header(
    out: &mut String,
    lang_name: &str,
    lang_name_lower: &str,
    section: &str,
    dead_rules_note: Option<&str>,
) {
    out.push_str(&format!(
        "// AUTO-GENERATED by language! macro for {} ({}) — do not edit\n",
        lang_name, section
    ));
    out.push_str("// Regenerated on each compilation of the language definition.\n");
    out.push_str("// Run with: cargo test -p mettail-languages\n\n");
    out.push_str("#![allow(unused_imports, dead_code)]\n\n");
    out.push_str(&format!("use mettail_languages::{}::*;\n", lang_name_lower));
    out.push_str("use mettail_runtime::Language;\n");
    out.push_str("use mettail_runtime::BehavioralPred;\n\n");

    if let Some(rules) = dead_rules_note {
        out.push_str(&format!("// Dead rules detected by WFST analysis: {}\n\n", rules));
    }
}

/// Delete a previously-written monolithic `gen_{lang}.rs` test file, if
/// it exists. The split-file emission (`gen_{lang}_unit.rs` etc.) may
/// redefine the same `#[test]` names, so the old file must go before
/// cargo sees both.
fn delete_stale_monolithic_file(lang_name: &str) {
    let filename = format!("gen_{}.rs", lang_name.to_lowercase());
    if let Ok(path) = get_test_output_path(&filename) {
        if path.exists() {
            let _ = std::fs::remove_file(&path);
        }
    }
}

/// Write one test-section file to disk.
fn write_test_section(lang_name: &str, section: &str, content: &str) {
    let filename = format!("gen_{}_{}.rs", lang_name.to_lowercase(), section);
    match get_test_output_path(&filename) {
        Ok(path) => {
            match write_if_changed(&path, content) {
                Ok(true) => {
                    eprintln!("  ({}) Generated test file: {}", lang_name, path.display());
                },
                Ok(false) => { /* unchanged; no mtime bump */ },
                Err(e) => {
                    eprintln!(
                        "Warning: Failed to write test file for {} ({}): {}",
                        lang_name, section, e
                    );
                },
            }
        },
        Err(e) => {
            eprintln!(
                "Warning: Failed to resolve test path for {} ({}): {}",
                lang_name, section, e
            );
        },
    }
}

/// Generate the per-constructor unit-test section (smallest; no helpers).
fn generate_unit_section(language: &LanguageDef, pipeline: &PipelineAnalysis) -> String {
    let lang_name = language.name.to_string();
    let lang_name_lower = lang_name.to_lowercase();
    let lang_struct = format!("{}Language", lang_name);

    let mut out = String::with_capacity(16384);
    // 2026-05-14: sort the dead-rules set into a Vec before formatting
    // so generated test files don't churn on each compile due to HashSet
    // iteration order. The set is informational (a comment), so any
    // deterministic ordering is fine; alphabetical reads cleanly.
    let dead_rules_str = if !pipeline.dead_rule_labels.is_empty() {
        let mut sorted: Vec<&String> = pipeline.dead_rule_labels.iter().collect();
        sorted.sort();
        Some(format!("{:?}", sorted))
    } else {
        None
    };
    emit_test_file_header(
        &mut out,
        &lang_name,
        &lang_name_lower,
        "unit",
        dead_rules_str.as_deref(),
    );

    out.push_str("// ═══════════════════════════════════════════════════════════\n");
    out.push_str("// Unit tests (one per constructor)\n");
    out.push_str("// ═══════════════════════════════════════════════════════════\n\n");

    // Language struct smoke test
    out.push_str("#[test]\n");
    out.push_str(&format!("fn {}_language_instantiates() {{\n", lang_name_lower));
    out.push_str(&format!("    let lang = {};\n", lang_struct));
    out.push_str(&format!("    assert_eq!(lang.name(), \"{}\");\n", lang_name));
    out.push_str("}\n\n");

    // Metadata non-empty
    out.push_str("#[test]\n");
    out.push_str(&format!("fn {}_metadata_populated() {{\n", lang_name_lower));
    out.push_str(&format!("    let lang = {};\n", lang_struct));
    out.push_str("    let meta = lang.metadata();\n");
    out.push_str(
        "    assert!(!meta.types().is_empty(), \"language should have at least one type\");\n",
    );
    out.push_str(
        "    assert!(!meta.terms().is_empty(), \"language should have at least one term\");\n",
    );
    out.push_str("}\n\n");

    // Per-constructor tests
    out.push_str(&unit_tests::generate_unit_tests(language, pipeline));
    out
}

/// Generate the property-test section (defines AnyTerm/TapeReader/build_*/arb_*
/// helpers and includes simulation tests that call `arb_*`).
fn generate_prop_section(language: &LanguageDef, pipeline: &PipelineAnalysis) -> String {
    let lang_name = language.name.to_string();
    let lang_name_lower = lang_name.to_lowercase();
    let mut out = String::with_capacity(32768);
    emit_test_file_header(&mut out, &lang_name, &lang_name_lower, "prop", None);

    out.push_str("// ═══════════════════════════════════════════════════════════\n");
    out.push_str("// Proptest strategies + property tests (tape-based)\n");
    out.push_str("// ═══════════════════════════════════════════════════════════\n\n");
    out.push_str(&strategies::generate_strategies(language));
    out.push('\n');

    // Simulation tests call `arb_*` strategies — keep them co-located so
    // the strategy-helper functions stay in the same compilation unit.
    out.push_str(&simulation_tests::generate_simulation_tests(language, pipeline));
    out
}

/// Generate the rewrite/equation tests section (no helpers required).
fn generate_rewrite_section(language: &LanguageDef, pipeline: &PipelineAnalysis) -> String {
    let lang_name = language.name.to_string();
    let lang_name_lower = lang_name.to_lowercase();
    let mut out = String::with_capacity(8192);
    emit_test_file_header(&mut out, &lang_name, &lang_name_lower, "rewrite", None);

    if !language.equations.is_empty() {
        out.push_str("// ═══════════════════════════════════════════════════════════\n");
        out.push_str("// Equation tests (one per equation)\n");
        out.push_str("// ═══════════════════════════════════════════════════════════\n\n");
        out.push_str(&equation_tests::generate_equation_tests(language));
    }

    if !language.rewrites.is_empty() {
        out.push_str("// ═══════════════════════════════════════════════════════════\n");
        out.push_str("// Rewrite tests (one per rewrite rule)\n");
        out.push_str("// ═══════════════════════════════════════════════════════════\n\n");
        out.push_str(&rewrite_tests::generate_rewrite_tests(language, pipeline));
    }

    out
}

/// Generate the operational-semantics tests section (all phases;
/// typically the largest, but helper-free so can stand alone).
fn generate_op_section(language: &LanguageDef, pipeline: &PipelineAnalysis) -> String {
    let lang_name = language.name.to_string();
    let lang_name_lower = lang_name.to_lowercase();
    let ops = operational_tests::generate_operational_tests(language, pipeline);
    if ops.trim().is_empty()
        || ops
            .trim()
            .starts_with("// No operational eval tests generated")
    {
        return String::new();
    }

    let mut out = String::with_capacity(ops.len() + 1024);
    emit_test_file_header(&mut out, &lang_name, &lang_name_lower, "op", None);
    out.push_str(&ops);
    out
}

/// Generate the analytical/user/program tests section (small).
fn generate_analytical_section(language: &LanguageDef, pipeline: &PipelineAnalysis) -> String {
    let lang_name = language.name.to_string();
    let lang_name_lower = lang_name.to_lowercase();

    let a = analytical_tests::generate_analytical_tests(language, pipeline);
    let u = user_tests::generate_user_tests(language);
    let p = program_tests::generate_program_tests(language);
    let ambiguity = ambiguity_exposure::generate_ambiguity_exposure_section(language).to_string();
    let binder = binder_shadowing::generate_binder_shadowing_section(language).to_string();
    let cross_cat = cross_cat_ambiguity::generate_cross_cat_ambiguity_section(language).to_string();
    let pratt_bp = pratt_bp_boundaries::generate_pratt_bp_boundaries_section(language).to_string();
    let recovery = recovery_corruption::generate_recovery_corruption_section(language).to_string();

    if a.trim().is_empty()
        && u.trim().is_empty()
        && p.trim().is_empty()
        && ambiguity.trim().is_empty()
        && binder.trim().is_empty()
        && cross_cat.trim().is_empty()
        && pratt_bp.trim().is_empty()
        && recovery.trim().is_empty()
    {
        return String::new();
    }

    let mut out = String::with_capacity(
        a.len()
            + u.len()
            + p.len()
            + ambiguity.len()
            + binder.len()
            + cross_cat.len()
            + pratt_bp.len()
            + recovery.len()
            + 1024,
    );
    emit_test_file_header(&mut out, &lang_name, &lang_name_lower, "analytical", None);
    push_analytical_subsection(&mut out, "__mettail_analytical", &a);
    push_analytical_subsection(&mut out, "__mettail_user_tests", &u);
    push_analytical_subsection(&mut out, "__mettail_program_tests", &p);
    push_analytical_subsection(&mut out, "__mettail_ambiguity_exposure", &ambiguity);
    push_analytical_subsection(&mut out, "__mettail_binder_shadowing", &binder);
    push_analytical_subsection(&mut out, "__mettail_cross_cat_ambiguity", &cross_cat);
    push_analytical_subsection(&mut out, "__mettail_pratt_bp_boundaries", &pratt_bp);
    push_analytical_subsection(&mut out, "__mettail_recovery_corruption", &recovery);
    out
}

fn push_analytical_subsection(out: &mut String, module_name: &str, content: &str) {
    if content.trim().is_empty() {
        return;
    }
    out.push_str("mod ");
    out.push_str(module_name);
    out.push_str(" {\n");
    out.push_str("use super::*;\n");
    out.push_str(content);
    out.push_str("\n}\n\n");
}

/// Generate the per-language simulation CLI binary source file.
/// Gated by `options { emit_simulator: true }` (default: true).
pub fn write_simulation_binary_if_enabled(language: &LanguageDef) {
    let emit = language
        .options
        .get("emit_simulator")
        .and_then(|v| match v {
            mettail_ast::language::AttributeValue::Bool(b) => Some(*b),
            _ => None,
        })
        .unwrap_or(true);
    if emit {
        simulation_binary::write_simulation_binary(language);
    }
}

// The old monolithic `generate_test_file` has been replaced by per-section
// `generate_*_section` functions above. See `write_test_file` for the new
// split-file emission orchestration.

// Note: The old inline `generate_analytical_tests()` function has been replaced
// by the `analytical_tests` module. The new module generates tests without any
// feature gates -- the testkit always links against prattail.

/// Group H: WFST static verification of Display parseability.
///
/// Checks that every constructor's label is known to the pipeline analysis.
/// If a constructor is in `dead_rule_labels`, warns that its Display output
/// may not be parseable. Called at codegen time (not at test time).
fn verify_display_parseability(language: &LanguageDef, pipeline: &PipelineAnalysis) {
    let lang_name = language.name.to_string();

    for rule in &language.terms {
        let label = rule.label.to_string();
        if pipeline.dead_rule_labels.contains(&label) {
            eprintln!(
                "  ({}) WFST warning: constructor {} is a dead rule — \
                 its Display output may not be parseable",
                lang_name, label
            );
        }
    }

    // Check auto-generated variants against dead rules
    for lang_type in &language.types {
        let cat = lang_type.name.to_string();
        let var_label = crate::gen::generate_var_label(&lang_type.name).to_string();
        if pipeline.dead_rule_labels.contains(&var_label) {
            eprintln!(
                "  ({}) WFST warning: auto-generated {} variable rule is a dead rule",
                lang_name, cat
            );
        }
        if let Some(native_type) = &lang_type.native_type {
            let lit_label = crate::gen::generate_literal_label(native_type).to_string();
            if pipeline.dead_rule_labels.contains(&lit_label) {
                eprintln!(
                    "  ({}) WFST warning: auto-generated {} literal rule is a dead rule",
                    lang_name, cat
                );
            }
        }
    }

    // Check for unreachable categories
    for cat in &pipeline.unreachable_categories {
        eprintln!(
            "  ({}) WFST warning: category {} is fully unreachable — all its rules are dead",
            lang_name, cat
        );
    }
}

/// Write content to a file only if it differs from what is already on disk.
///
/// Skipping the write when content is unchanged prevents cargo from seeing a
/// newer mtime on generated files and triggering spurious recompilation of the
/// entire `mettail-languages` crate on every build.
///
/// Returns `true` if the file was written, `false` if it was unchanged.
fn write_if_changed(path: &std::path::Path, content: &str) -> std::io::Result<bool> {
    if let Ok(existing) = std::fs::read_to_string(path) {
        if existing == content {
            return Ok(false);
        }
    }
    std::fs::write(path, content)?;
    Ok(true)
}

/// Get the output path for generated test files.
///
/// Targets `languages/tests/` directly (not a subdirectory) so cargo
/// auto-discovers them. Uses `gen_` prefix to distinguish from hand-written tests.
fn get_test_output_path(filename: &str) -> std::io::Result<PathBuf> {
    // CARGO_MANIFEST_DIR points to macros/ — go up to workspace root
    let manifest_dir = std::env::var("CARGO_MANIFEST_DIR").unwrap_or_else(|_| ".".to_string());

    let mut path = PathBuf::from(manifest_dir);
    path.pop(); // Go up from macros/ to workspace root
    path.push("languages");
    path.push("tests");

    // Create directory if it doesn't exist
    std::fs::create_dir_all(&path)?;

    path.push(filename);
    Ok(path)
}
