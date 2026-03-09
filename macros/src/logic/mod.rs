//! Ascent Datalog code generation
//!
//! This module orchestrates the generation of Ascent Datalog code for a theory.
//!
//! ## Structure
//!
//! - `relations` - Relation declarations (categories, equality, rewrites, projections)
//! - `categories` - Category exploration and term deconstruction rules
//! - `equations` - Equality/equation rules with congruence
//! - `rewrites/` - Base rewrite rules and pattern/RHS generation
//! - `congruence/` - Congruence rules for rewrites (collection, regular, binding)
//!
//! ## Generated Code Components
//!
//! 1. **Relations**: Declare all Ascent relations for terms, equality, and rewrites
//! 2. **Category Rules**: Explore term space via rewrites and deconstruct terms
//! 3. **Equation Rules**: Add reflexivity, congruence, and user-defined equalities
//! 4. **Rewrite Rules**: Base rewrites + congruence rules (propagate through constructors)

use crate::ast::grammar::{GrammarItem, TermParam};
use crate::ast::types::{EvalMode, TypeExpr};
use crate::{ast::language::LanguageDef, logic::rules::generate_base_rewrites};
use common::{in_cat_filter, CategoryFilter};
use std::collections::{BTreeMap, BTreeSet, HashSet};
use proc_macro2::{Ident, TokenStream};
use quote::{format_ident, quote};

mod antipattern;
mod bloom_filter;
mod categories;
pub mod common;
mod equations;
pub mod fusion;
pub mod helpers;
mod pattern_codec;
pub mod pattern_trie;
mod relations;
mod writer;

pub mod congruence;
pub mod rules;

// Re-export key functions
pub use categories::generate_category_rules;
pub use equations::generate_equation_rules;
// BCG06: Stratified equation evaluation — re-export for cross-module access.
#[allow(unused_imports)]
pub use equations::{stratify_equation_rules, EqRuleKind, StratificationInfo};
pub use relations::generate_relations;
pub use relations::list_all_relations_for_extraction;

// Re-export congruence function
pub use congruence::generate_all_explicit_congruences;

/// Build a structured lint diagnostic for the PraTTaIL lint system.
///
/// Returns the diagnostic for local collection. Callers accumulate diagnostics
/// and emit them in batch (with optional grouping) at the end of each analysis section.
fn build_lint(
    id: &'static str,
    name: &'static str,
    severity: mettail_prattail::lint::LintSeverity,
    message: String,
    hint: Option<String>,
    grammar_name: Option<String>,
) -> mettail_prattail::lint::LintDiagnostic {
    mettail_prattail::lint::LintDiagnostic {
        id,
        name,
        severity,
        category: None,
        rule: None,
        message,
        hint,
        grammar_name,
        source_location: None,
    }
}

/// Group and emit a batch of collected diagnostics.
///
/// When `PRATTAIL_LINT_VERBOSE` is set, emits individual diagnostics.
/// Otherwise, groups repeated lint IDs into compact summaries.
fn emit_collected_diagnostics(diagnostics: Vec<mettail_prattail::lint::LintDiagnostic>) {
    if diagnostics.is_empty() {
        return;
    }
    let verbose = std::env::var("PRATTAIL_LINT_VERBOSE").is_ok();
    let to_emit = if verbose {
        diagnostics
    } else {
        mettail_prattail::lint::group_diagnostics(diagnostics)
    };
    for diag in &to_emit {
        mettail_prattail::lint::emit_diagnostic(diag);
    }
}

/// Output from Ascent source generation
pub struct AscentSourceOutput {
    /// Full output including helper functions and ascent_source! wrapper (for debug dump & backward compat)
    pub full_output: TokenStream,
    /// Raw Ascent content (relations + rules) without ascent_source! wrapper, suitable for direct
    /// inclusion in an `ascent! { struct Foo; #raw_content }` invocation.
    pub raw_content: TokenStream,
    /// Core Ascent content for the "core" struct (fewer rules, same relations).
    /// Only `Some` for multi-category languages where core != full.
    /// Used for SCC splitting: the core struct has fewer rules in its fixpoint loop.
    pub core_raw_content: Option<TokenStream>,
    /// Pre-stratum content: ground HOL step rules + deconstruction + category expansion.
    /// Evaluated in a separate Ascent struct before the main fixpoint, converging
    /// in O(depth) iterations. Only `Some` when ground HOL step rules exist.
    /// The main fixpoint is then seeded with the pre-stratum's results.
    pub pre_stratum_content: Option<TokenStream>,
    /// B-CG04: Ground rewrite seed tuples.
    ///
    /// Each entry is a `TokenStream` fragment of the form:
    ///   `prog.rw_cat.push((lhs_expr, rhs_expr));`
    /// that directly seeds the rewrite relation at Ascent initialization,
    /// bypassing per-iteration pattern matching for fully ground LHS rewrites.
    pub ground_rewrite_seeds: Vec<TokenStream>,
}

/// Main entry point: Generate complete Ascent source for a theory.
///
/// When `analysis` is provided, WFST-derived data (dead rules, constructor
/// weights, category weights) is used to optimize generated Ascent code:
/// - Dead-code elimination of rules referencing dead constructors (Sprint 1)
/// - WFST-weight-guided rule ordering for cache locality (Sprint 3)
/// - Constructor-weight-based match arm ordering (Sprint 4)
///
/// When `analysis` is `None`, all rules are generated unconditionally
/// (backward compatible behavior).
pub fn generate_ascent_source(
    language: &LanguageDef,
    analysis: Option<&mettail_prattail::PipelineAnalysis>,
) -> AscentSourceOutput {
    let grammar_name = language.name.to_string();
    let theory_name = grammar_name.to_lowercase();
    let source_name = format_ident!("{}_source", theory_name);

    // Sprint A (N10): Compute subsumed equation set for DCE.
    // Only equations are eligible for subsumption elimination because equations
    // are symmetric (LHS ≡ RHS), so RHS subsumption is automatic.
    // Rewrite subsumption would require separate RHS analysis (deferred).
    let subsumed_equations = compute_subsumed_equations(language, &grammar_name);

    // Detect cancellation pairs: equations of the form Outer(Inner(X)) = X.
    // These are suppressed from eqrel generation (would cause non-convergence)
    // and handled by normalize arms + directional rewrites instead.
    let (cancellation_pairs, cancellation_equations) =
        crate::ast::pattern::detect_cancellation_pairs(language);
    emit_cancellation_pair_lints(&cancellation_pairs, language, &grammar_name);

    // A-RT05: Compile-time depth delta analysis.
    // Analyze equation/rewrite patterns for depth-increasing rules that could
    // cause fixpoint non-convergence.
    emit_depth_delta_lints(language, &grammar_name);

    // A-RT02: Semi-naive delta guard analysis.
    // Analyze the rule-relation dependency graph to identify delta groups,
    // always-active rules, and feedback cycles in the generated Ascent code.
    emit_delta_guard_lints(language, &grammar_name);

    // C-AP01 through C-AP05: Ascent antipattern detection.
    // Detects common performance antipatterns in user-defined logic blocks,
    // grammar constructors, and rewrite rules.
    emit_antipattern_lints(language, &grammar_name);

    // BCG05: Normalize-on-insert deduplication diagnostic.
    // The hash-based dedup guards are unconditionally emitted in the generated
    // Ascent code (categories.rs and rules.rs). Emit a single G41 note so the
    // user knows the optimization is active.
    {
        let rule_count = language.equations.len() + language.rewrites.len();
        let cat_count = language.types.len();
        mettail_prattail::lint::emit_diagnostic(&build_lint(
            "G41", "normalize-dedup-active",
            mettail_prattail::lint::LintSeverity::Note,
            format!(
                "BCG05 normalize-on-insert dedup: hash guards emitted for {} rule(s) across {} category(ies)",
                rule_count, cat_count,
            ),
            Some("structural hash pre-check avoids redundant normalize() calls in the Ascent fixpoint".to_string()),
            Some(grammar_name.clone()),
        ));
    }

    // BCG02: Rule fusion analysis for chained deconstruction-rewrite patterns.
    // Detects chains where a deconstruction rule extracts subterms that are then
    // matched by a rewrite rule, producing intermediate tuples that could be
    // eliminated by fusing the two rules. Emits G42 diagnostics with the analysis
    // results (safe/blocked candidates and estimated tuple reduction).
    fusion::emit_fusion_diagnostics(language, &grammar_name);

    // ART06 Extended Demand Filtering: compute demanded categories once and share
    // across all codegen functions. Categories not in the demanded set have no
    // equation/rewrite/logic rule referencing them, so their eq/rw/fold relations
    // and associated rules are dead code.
    let demanded = common::compute_demanded_categories(language);

    // BCG06: Compute stratification once for both diagnostics and rule ordering.
    let strat_info = stratify_equation_rules(language);

    // BCG06: Stratified equation evaluation diagnostic.
    // Performs SCC-based stratification analysis of equation rules (reflexivity,
    // congruence, user-defined) and emits a diagnostic note summarizing the
    // stratum structure. This informs the user about the dependency layers
    // in their equation rules.
    {
        if strat_info.total_rules > 0 {
            let stratum_details: Vec<String> = strat_info
                .strata
                .iter()
                .map(|s| {
                    let kinds: Vec<String> = s.rules.iter().map(|r| r.label.clone()).collect();
                    format!("stratum {}: [{}]", s.index, kinds.join(", "))
                })
                .collect();
            let verbose = std::env::var("PRATTAIL_LINT_VERBOSE").is_ok();
            let hint_text = if verbose || stratum_details.len() <= 5 {
                stratum_details.join("; ")
            } else {
                // Truncate for readability; full listing available via PRATTAIL_LINT_VERBOSE
                let mut truncated = stratum_details[..5].to_vec();
                truncated.push(format!("... and {} more strata (set PRATTAIL_LINT_VERBOSE=1 to see all)", stratum_details.len() - 5));
                truncated.join("; ")
            };
            mettail_prattail::lint::emit_diagnostic(&build_lint(
                "G42", "eq-strata-analysis",
                mettail_prattail::lint::LintSeverity::Note,
                format!(
                    "BCG06 equation stratification: {}",
                    strat_info,
                ),
                Some(hint_text),
                Some(grammar_name.clone()),
            ));
        }
    }

    let helper_fns = helpers::generate_helper_functions(language);
    let relations = generate_relations(language, &demanded);
    let category_rules = generate_category_rules(language, None);
    let equation_rules = generate_equation_rules(language, None, analysis, &subsumed_equations, &cancellation_equations, true, &demanded, Some(&strat_info));
    let rewrite_rules = generate_rewrite_rules(language, None, analysis, true, &demanded);

    // BCG02: Generate fused rules for safe deconstruction-rewrite chains.
    // These are ADDITIVE — the original unfused rules remain. The fused rules
    // provide an alternative derivation path that fires in the same iteration
    // as the parent deconstruction, eliminating the intermediate tuple step.
    let (fused_rules, fused_count) = fusion::generate_all_fused_rules(language);
    let fused_content = if fused_rules.is_empty() {
        quote! {}
    } else {
        // Emit diagnostic for fused rule generation
        mettail_prattail::lint::emit_diagnostic(&build_lint(
            "G42", "rule-fusion-codegen",
            mettail_prattail::lint::LintSeverity::Note,
            format!(
                "BCG02: {} fused rule(s) generated for safe deconstruction-rewrite chains",
                fused_count,
            ),
            Some("fused rules provide an alternative derivation path, eliminating intermediate tuples".to_string()),
            Some(grammar_name.clone()),
        ));
        quote! { #(#fused_rules)* }
    };

    let custom_logic = language
        .logic
        .as_ref()
        .map(|l| l.content.clone())
        .unwrap_or_default();

    let raw_content = quote! {
        #relations

        #category_rules

        #equation_rules

        #rewrite_rules

        #fused_content

        #custom_logic
    };

    // Generate core content if this is a multi-category language with non-trivial core
    let core_raw_content = common::compute_core_categories(language).map(|core_cats| {
        let core_relations = generate_relations(language, &demanded);
        let core_category_rules = generate_category_rules(language, Some(&core_cats));
        let core_equation_rules = generate_equation_rules(language, Some(&core_cats), analysis, &subsumed_equations, &cancellation_equations, false, &demanded, Some(&strat_info));
        let core_rewrite_rules = generate_rewrite_rules(language, Some(&core_cats), analysis, false, &demanded);

        quote! {
            #core_relations

            #core_category_rules

            #core_equation_rules

            #core_rewrite_rules

            #custom_logic
        }
    });

    let full_output = quote! {
        #helper_fns

        ::ascent::ascent_source! {
            #source_name:

            #raw_content
        }
    };

    // Format and write the generated Ascent source to file
    let formatted_source = format_ascent_source(
        &theory_name,
        &source_name,
        &relations,
        &category_rules,
        &equation_rules,
        &rewrite_rules,
        &custom_logic,
    );

    // Write to file for inspection
    if let Err(e) = writer::write_ascent_file(&grammar_name, &theory_name, &formatted_source) {
        // I10 emits immediately (one-off infrastructure diagnostic, not groupable)
        mettail_prattail::lint::emit_diagnostic(&build_lint(
            "I10", "ascent-file-write-failed",
            mettail_prattail::lint::LintSeverity::Warning,
            format!("failed to write Ascent Datalog file: {}", e),
            Some("check directory permissions".to_string()),
            Some(grammar_name.clone()),
        ));
    }

    // Sprint 6: Pattern trie analysis for fine-grained dependency stratification
    // Build the PatternIndex from equations and rewrites, then compute:
    // - Fine-grained dependency groups (connected components by constructor label)
    // - Alpha-equivalent LHS pattern groups (same De Bruijn bytes → shared matching code)
    // - Subsumption warnings (general pattern subsumes specific pattern)
    if !language.equations.is_empty() || !language.rewrites.is_empty() {
        let pattern_index = pattern_trie::PatternIndex::build(language);
        let dep_groups = pattern_trie::compute_fine_dependency_groups(&pattern_index);
        let alpha_groups = pattern_trie::find_alpha_equivalent_groups(&pattern_index);
        let subsumptions = pattern_trie::detect_subsumption(&pattern_index);

        // Collect diagnostics locally for batch grouping
        let mut macro_diagnostics = Vec::new();

        if !subsumptions.is_empty() {
            for sub in &subsumptions {
                let general_name = rule_id_name(sub.general, language);
                let specific_name = rule_id_name(sub.specific, language);
                let eliminated = if let (
                    pattern_trie::RuleId::Equation(_),
                    pattern_trie::RuleId::Equation(i),
                ) = (sub.general, sub.specific) {
                    subsumed_equations.contains(&i)
                } else {
                    false
                };
                if eliminated {
                    macro_diagnostics.push(build_lint(
                        "G26", "equation-subsumed",
                        mettail_prattail::lint::LintSeverity::Note,
                        format!("equation `{}` eliminated — subsumed by more general equation `{}`", specific_name, general_name),
                        Some(format!("the more general equation `{}` covers all cases", general_name)),
                        Some(grammar_name.clone()),
                    ));
                } else {
                    macro_diagnostics.push(build_lint(
                        "G27", "rule-subsumption-candidate",
                        mettail_prattail::lint::LintSeverity::Warning,
                        format!(
                            "rule `{}` may be subsumed by more general rule `{}` \
                             (both LHS patterns match the same terms, but `{}` is more general)",
                            specific_name, general_name, general_name,
                        ),
                        Some(format!("review whether rule `{}` can be removed or merged with `{}`", specific_name, general_name)),
                        Some(grammar_name.clone()),
                    ));
                }
            }
        }

        if !alpha_groups.is_empty() {
            let group_count = alpha_groups.len();
            let total_rules: usize = alpha_groups.iter().map(|g| g.len()).sum();
            macro_diagnostics.push(build_lint(
                "G28", "alpha-equivalent-groups",
                mettail_prattail::lint::LintSeverity::Note,
                format!(
                    "{} alpha-equivalent LHS pattern group(s) detected ({} rules total) \
                     — these rules share identical matching structure",
                    group_count, total_rules,
                ),
                Some("these rules share identical matching structure and may benefit from consolidation".to_string()),
                Some(grammar_name.clone()),
            ));
        }

        // Log dependency group analysis
        let independent = dep_groups.iter().filter(|g| g.len() == 1).count();
        if dep_groups.len() > 1 {
            macro_diagnostics.push(build_lint(
                "G29", "dependency-groups",
                mettail_prattail::lint::LintSeverity::Note,
                format!(
                    "{} fine-grained dependency group(s) detected ({} independent, {} cross-group)",
                    dep_groups.len(), independent, dep_groups.len() - independent,
                ),
                Some("independent groups can be evaluated in separate strata for performance".to_string()),
                Some(grammar_name.clone()),
            ));
        }

        emit_collected_diagnostics(macro_diagnostics);

        // Sprint 6g/6h Extension Point: Multi-stratum codegen
        //
        // The dependency groups above identify rules that can be evaluated
        // independently. When a grammar has large independent groups (≥3 rules
        // each), generating separate Ascent structs per group and chaining them
        // (pre-stratum → per-group strata → main fixpoint) would reduce the
        // main SCC's working set.
        //
        // Currently deferred because:
        // 1. Each additional `ascent!` struct adds ~5-10s compilation time
        // 2. The grammars tested so far have mostly single-rule independent
        //    groups (25/66 in RhoCalc), where the compilation overhead
        //    would exceed runtime savings
        // 3. The pre-stratum (Sprint 5) already handles the highest-impact
        //    case (ground HOL step rules)
        //
        // Activation condition: when a grammar has ≥2 independent groups
        // with ≥5 rules each, generate per-group Ascent strata using
        // `generate_stratified_content()` and `group_categories()`.
        //
        // Implementation plan (see Sprint 6g/6h in the plan):
        // 1. For each independent group ≥5 rules:
        //    a. Compute the group's category set via group_categories()
        //    b. Generate relations for those categories only
        //    c. Generate category rules filtered to those categories
        //    d. Generate equation/rewrite rules for only the group's rules
        //    e. Emit as a separate AscentSourceOutput.stratum_contents entry
        // 2. In language.rs, generate per-stratum Ascent structs
        // 3. Chain: pre-stratum → per-group strata → main fixpoint
        let _ = &dep_groups;
        let _ = &alpha_groups;
    }

    // Sprint 8: Log isomorphic WFST groups if detected
    if let Some(ref a) = analysis {
        if !a.isomorphic_groups.is_empty() {
            let total_cats: usize = a.isomorphic_groups.iter().map(|g| g.len()).sum();
            let group_lines: Vec<String> = a.isomorphic_groups.iter().enumerate()
                .map(|(i, group)| format!("  group {}: [{}]", i, group.join(", ")))
                .collect();
            mettail_prattail::lint::emit_diagnostic(&build_lint(
                "G30", "isomorphic-wfst-groups",
                mettail_prattail::lint::LintSeverity::Note,
                format!(
                    "{} isomorphic WFST group(s) detected ({} categories total) \
                     — these categories share identical dispatch topology\n{}",
                    a.isomorphic_groups.len(), total_cats, group_lines.join("\n"),
                ),
                Some("categories with identical topology can share a single WFST".to_string()),
                Some(grammar_name.clone()),
            ));
        }
    }

    // Sprint 5: Generate pre-stratum content if ground HOL step rules exist.
    // The pre-stratum evaluates ground rewrites in O(depth) iterations before
    // the main fixpoint, reducing SCC iteration count.
    let pre_stratum_content = generate_pre_stratum_content(language, analysis);

    // B-CG04: Detect ground-LHS rewrite rules and generate seed tuples.
    // These are pushed into rw_cat at Ascent initialization (iteration 0),
    // making the rewrite result immediately available without fixpoint scanning.
    let (ground_rewrite_seeds, ground_count) =
        rules::generate_ground_rewrite_seeds(language);
    if ground_count > 0 {
        emit_collected_diagnostics(vec![build_lint(
            "G35",
            "ground-rewrite-short-circuit",
            mettail_prattail::lint::LintSeverity::Note,
            format!(
                "{} ground-LHS rewrite(s) detected — results seeded at initialization (B-CG04)",
                ground_count,
            ),
            Some("ground rewrites produce statically known results; seeding avoids per-iteration scanning".to_string()),
            Some(grammar_name.clone()),
        )]);
    }

    AscentSourceOutput {
        full_output,
        raw_content,
        core_raw_content,
        pre_stratum_content,
        ground_rewrite_seeds,
    }
}

/// Get a human-readable name for a RuleId.
fn rule_id_name(id: pattern_trie::RuleId, language: &LanguageDef) -> String {
    match id {
        pattern_trie::RuleId::Equation(i) => {
            language.equations.get(i)
                .map(|eq| eq.name.to_string())
                .unwrap_or_else(|| format!("equation[{}]", i))
        }
        pattern_trie::RuleId::Rewrite(i) => {
            language.rewrites.get(i)
                .map(|rw| rw.name.to_string())
                .unwrap_or_else(|| format!("rewrite[{}]", i))
        }
    }
}

/// Compute the set of equation indices that are subsumed by more general equations.
///
/// A subsumed equation's LHS pattern matches a strict subset of terms matched by
/// the general equation. Since equations are symmetric (LHS ≡ RHS), the general
/// equation fires for ALL terms the subsumed equation would match and produces
/// the SAME derived `eq_cat` facts. Therefore, removing the subsumed equation
/// does not change the fixpoint.
///
/// Only equations are eligible — rewrite subsumption requires separate RHS
/// analysis because rewrites are directional (deferred to future sprint).
///
/// Returns a `HashSet<usize>` of equation indices into `language.equations`.
fn compute_subsumed_equations(language: &LanguageDef, grammar_name: &str) -> HashSet<usize> {
    if language.equations.is_empty() && language.rewrites.is_empty() {
        return HashSet::new();
    }

    let pattern_index = pattern_trie::PatternIndex::build(language);
    let subsumptions = pattern_trie::detect_subsumption(&pattern_index);

    let mut subsumed = HashSet::new();
    for pair in &subsumptions {
        // Only eliminate subsumed equations (not rewrites).
        // The general rule must also be an equation for correctness:
        // equation symmetry guarantees RHS subsumption is automatic.
        if let (
            pattern_trie::RuleId::Equation(_),
            pattern_trie::RuleId::Equation(specific_idx),
        ) = (pair.general, pair.specific) {
            subsumed.insert(specific_idx);
        }
    }

    if !subsumed.is_empty() {
        mettail_prattail::lint::emit_diagnostic(&build_lint(
            "G31", "subsumed-equations-eliminated",
            mettail_prattail::lint::LintSeverity::Note,
            format!("{} subsumed equation(s) eliminated from Ascent codegen", subsumed.len()),
            Some("subsumed equations are redundant and have been removed from Ascent codegen".to_string()),
            Some(grammar_name.to_string()),
        ));
    }

    subsumed
}

/// Emit lint diagnostics for detected cancellation pairs.
///
/// **G25 (note)**: Fires for every suppressed cancellation pair equation.
/// Informational: tells the user that the equation was detected as a
/// cancellation pair and will be handled by `normalize()` instead of `eqrel`.
///
/// **W09 (warning)**: Fires when a cancellation pair equation is suppressed
/// but no corresponding directional rewrite exists to cover the same pattern.
/// Without the rewrite, the cancellation pair can only be collapsed during
/// `normalize()` calls, not during Ascent's fixpoint iteration. This is only
/// a problem for categories with explicit congruence rewrites (which can
/// introduce the cancellation pattern at runtime).
fn emit_cancellation_pair_lints(
    pairs: &[crate::ast::pattern::CancellationPair],
    language: &LanguageDef,
    grammar_name: &str,
) {
    use crate::ast::pattern::{Pattern, PatternTerm};

    for pair in pairs {
        let eq_rel = pair.outer_category.to_string().to_lowercase();

        // G25: note — cancellation pair detected and suppressed
        mettail_prattail::lint::emit_diagnostic(&build_lint(
            "G25", "cancellation-pair-detected",
            mettail_prattail::lint::LintSeverity::Note,
            format!("equation `{}` is a cancellation pair and has been suppressed", pair.equation_name),
            Some(format!(
                "{}({}(X)) = X is handled by normalize() instead of eq_{}",
                pair.outer_constructor, pair.inner_constructor, eq_rel,
            )),
            Some(grammar_name.to_string()),
        ));

        // W09: check if a corresponding directional rewrite exists
        let has_corresponding_rewrite = language.rewrites.iter().any(|rw| {
            // Check if LHS is Outer(Inner(Var(X))) and RHS is Var(X)
            match (&rw.left, &rw.right) {
                (
                    Pattern::Term(PatternTerm::Apply {
                        constructor: outer,
                        args: outer_args,
                    }),
                    Pattern::Term(PatternTerm::Var(rhs_var)),
                ) if outer == &pair.outer_constructor && outer_args.len() == 1 => {
                    // Check inner: Apply(inner_ctor, [Var(X)])
                    match &outer_args[0] {
                        Pattern::Term(PatternTerm::Apply {
                            constructor: inner,
                            args: inner_args,
                        }) if inner == &pair.inner_constructor && inner_args.len() == 1 => {
                            // Check innermost is Var(X) matching RHS
                            match &inner_args[0] {
                                Pattern::Term(PatternTerm::Var(lhs_var)) => {
                                    lhs_var.to_string() == rhs_var.to_string()
                                }
                                _ => false,
                            }
                        }
                        _ => false,
                    }
                }
                _ => false,
            }
        });

        if !has_corresponding_rewrite {
            // Only warn if the category has explicit congruence rewrites.
            // Categories without congruences (e.g., Name) won't introduce the
            // cancellation pattern at runtime, so the missing rewrite is harmless.
            let cat_str = pair.outer_category.to_string();
            let has_congruence_rewrites = language.rewrites.iter().any(|rw| {
                rw.is_congruence_rule()
                    && rw
                        .left
                        .category(language)
                        .map(|c| c.to_string())
                        == Some(cat_str.clone())
            });

            if has_congruence_rewrites {
                mettail_prattail::lint::emit_diagnostic(&build_lint(
                    "W09", "cancellation-pair-missing-rewrite",
                    mettail_prattail::lint::LintSeverity::Warning,
                    format!("cancellation pair `{}` has no corresponding rewrite", pair.equation_name),
                    Some(format!(
                        "add `|- ({} ({} X)) ~> X ;` to ensure runtime reduction; \
                         without this rewrite, {}({}(X)) can only be collapsed by normalize()",
                        pair.outer_constructor, pair.inner_constructor,
                        pair.outer_constructor, pair.inner_constructor,
                    )),
                    Some(grammar_name.to_string()),
                ));
            }
        }
    }
}

/// A-RT05: Emit compile-time lint diagnostics for depth delta analysis.
///
/// Analyzes all equation/rewrite patterns and warns when:
/// - Individual rules have positive depth delta (depth-increasing)
/// - The grammar as a whole is not depth-bounded (fixpoint may not converge)
fn emit_depth_delta_lints(language: &LanguageDef, grammar_name: &str) {
    if language.equations.is_empty() && language.rewrites.is_empty() {
        return;
    }

    let results = rules::analyze_depth_delta(language);
    if results.is_empty() {
        return;
    }

    let is_bounded = rules::is_depth_bounded(&results);

    let mut diagnostics = Vec::new();

    // Collect individual depth-increasing rules
    let increasing: Vec<&rules::DepthDeltaResult> = results.iter().filter(|r| r.delta > 0).collect();

    for r in &increasing {
        let rule_kind = if r.is_equation { "equation" } else { "rewrite" };

        // Derive the category from the equation/rewrite's LHS pattern
        let category = if r.is_equation {
            language.equations.iter()
                .find(|eq| eq.name.to_string() == r.rule_name)
                .and_then(|eq| eq.left.category(language))
                .map(|c| c.to_string())
        } else {
            language.rewrites.iter()
                .find(|rw| rw.name.to_string() == r.rule_name)
                .and_then(|rw| rw.left.category(language))
                .map(|c| c.to_string())
        };

        diagnostics.push(mettail_prattail::lint::LintDiagnostic {
            id: "A01",
            name: "depth-increasing-rule",
            severity: mettail_prattail::lint::LintSeverity::Note,
            category,
            rule: Some(r.rule_name.clone()),
            message: format!(
                "{} `{}` is depth-increasing (LHS depth {}, RHS depth {}, delta +{})",
                rule_kind, r.rule_name, r.lhs_depth, r.rhs_depth, r.delta,
            ),
            hint: Some(
                "depth-increasing rules can cause unbounded term growth during fixpoint computation; \
                 consider whether a complementary depth-reducing rule exists"
                    .to_string(),
            ),
            grammar_name: Some(grammar_name.to_string()),
            source_location: None,
        });
    }

    // Summary diagnostic: bounded vs unbounded
    if is_bounded {
        diagnostics.push(build_lint(
            "A01",
            "depth-bounded-grammar",
            mettail_prattail::lint::LintSeverity::Note,
            format!(
                "all {} equation/rewrite rules are depth-non-increasing — fixpoint convergence guaranteed",
                results.len(),
            ),
            None,
            Some(grammar_name.to_string()),
        ));
    } else if !increasing.is_empty() {
        diagnostics.push(build_lint(
            "A01",
            "depth-unbounded-grammar",
            mettail_prattail::lint::LintSeverity::Warning,
            format!(
                "grammar has {} depth-increasing rule(s) out of {} total — \
                 fixpoint may not converge without runtime depth bound (A-RT05)",
                increasing.len(),
                results.len(),
            ),
            Some(
                "a runtime depth bound of 100 is applied to detect non-convergence; \
                 review depth-increasing rules or increase the bound if needed"
                    .to_string(),
            ),
            Some(grammar_name.to_string()),
        ));
    }

    emit_collected_diagnostics(diagnostics);
}

// ══════════════════════════════════════════════════════════════════════════════
// C-AP01 through C-AP05: Ascent Antipattern Detection
// ══════════════════════════════════════════════════════════════════════════════

/// Emit lint diagnostics for all detected Ascent antipatterns.
///
/// Runs the five antipattern detectors (C-AP01 through C-AP05) and emits
/// collected diagnostics via the PraTTaIL lint system.
fn emit_antipattern_lints(language: &LanguageDef, grammar_name: &str) {
    let ap_warnings = antipattern::detect_antipatterns(language);
    if ap_warnings.is_empty() {
        return;
    }

    let diagnostics: Vec<mettail_prattail::lint::LintDiagnostic> = ap_warnings
        .iter()
        .map(|w| {
            let severity = match w.code {
                // C-AP01 and C-AP04 are performance warnings (cubic blowup, non-convergence)
                "C-AP01" | "C-AP04" => mettail_prattail::lint::LintSeverity::Warning,
                // C-AP02 is a performance warning (quadratic blowup)
                "C-AP02" => mettail_prattail::lint::LintSeverity::Warning,
                // C-AP03 and C-AP05 are notes (informational)
                _ => mettail_prattail::lint::LintSeverity::Note,
            };
            build_lint(
                // Map antipattern code to a lint id (reuse the code as id)
                match w.code {
                    "C-AP01" => "C-AP01",
                    "C-AP02" => "C-AP02",
                    "C-AP03" => "C-AP03",
                    "C-AP04" => "C-AP04",
                    "C-AP05" => "C-AP05",
                    _ => "C-AP00", // should not happen
                },
                match w.code {
                    "C-AP01" => "cubic-transitivity-blowup",
                    "C-AP02" => "quadratic-extension-along-equality",
                    "C-AP03" => "deep-congruence-chain",
                    "C-AP04" => "unbounded-rewrite-growth",
                    "C-AP05" => "clone-storm-collection-field",
                    _ => "unknown-antipattern",
                },
                severity,
                w.message.clone(),
                w.hint.clone(),
                Some(grammar_name.to_string()),
            )
        })
        .collect();

    emit_collected_diagnostics(diagnostics);
}

// ══════════════════════════════════════════════════════════════════════════════
// A-RT02: Incremental Semi-Naive Delta Guard Analysis
// ══════════════════════════════════════════════════════════════════════════════

/// A generated Ascent rule descriptor for dependency analysis.
///
/// Captures which relations a rule reads (body) and writes (head),
/// enabling compile-time analysis of the fixpoint iteration structure.
#[derive(Debug, Clone)]
struct RuleDescriptor {
    /// Human-readable rule name (e.g., "reflexivity/Proc", "eq-congruence/Proc/Name").
    name: String,
    /// Rule kind for grouping.
    kind: RuleKind,
    /// Relations read in the rule body (e.g., `["proc", "eq_name"]`).
    body_relations: BTreeSet<String>,
    /// Relations written in the rule head (e.g., `["eq_proc"]`).
    head_relations: BTreeSet<String>,
}

/// Classification of generated rule kinds.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum RuleKind {
    /// `eq_cat(t, t) <-- cat(t);`
    Reflexivity,
    /// `eq_cat(s, t) <-- cat(s), cat(t), eq_fld(sf, tf), ...;`
    EqCongruence,
    /// `eq_cat(s, t), cat(t) <-- cat(s), if let ...;`
    UserEquation,
    /// `rw_cat(s_orig, t) <-- eq_cat(s_orig, s), if let ...;`
    BaseRewrite,
    /// `rw_cat(s, t) <-- cat(s), rw_fld(fld, fld'), ...;` (HOL step)
    HolStep,
    /// `fold_cat(s, t) <-- cat(s), ...;`
    Fold,
    /// `rw_cat(s, t) <-- cat(s), rw_fld(s_f, t_f), ...;` (explicit congruence)
    ExplicitCongruence,
    /// `rw_cat(a, c) <-- eq_cat(a, b), rw_cat(b, c);`
    EqRwClosure,
    /// `cat(c1) <-- cat(c0), rw_cat(c0, c1);`
    CategoryExpansion,
    /// `tgt(field) <-- cat(s), if let ...;`
    Deconstruction,
}

impl RuleKind {
    fn label(self) -> &'static str {
        match self {
            RuleKind::Reflexivity => "reflexivity",
            RuleKind::EqCongruence => "eq-congruence",
            RuleKind::UserEquation => "user-equation",
            RuleKind::BaseRewrite => "base-rewrite",
            RuleKind::HolStep => "hol-step",
            RuleKind::Fold => "fold",
            RuleKind::ExplicitCongruence => "explicit-congruence",
            RuleKind::EqRwClosure => "eq-rw-closure",
            RuleKind::CategoryExpansion => "category-expansion",
            RuleKind::Deconstruction => "deconstruction",
        }
    }
}

/// Result of the A-RT02 semi-naive delta guard analysis.
#[derive(Debug)]
struct DeltaGuardAnalysis {
    /// Total number of generated Ascent rules.
    total_rules: usize,
    /// Rules grouped by their body relation signature (set of body relations).
    /// Rules with the same body signature form a "delta group": they become
    /// active under exactly the same conditions (when any shared body relation
    /// has new tuples).
    delta_groups: BTreeMap<BTreeSet<String>, Vec<String>>,
    /// Rules that reference >= 3 distinct body relations from different families.
    /// These are "always-active" during fixpoint: at least one of their body
    /// relations is likely to have deltas each iteration, so they cannot be
    /// skipped by a simple delta guard.
    always_active_rules: Vec<String>,
    /// Feedback cycles: relations that appear in both head and body of the same
    /// rule (self-loops in the rule-relation dependency graph).
    feedback_relations: BTreeSet<String>,
    /// Number of distinct relation families (cat, eq, rw, fold, projection, custom).
    relation_family_count: usize,
    /// Per-rule-kind breakdown of rule counts (for diagnostic summary).
    rule_kind_counts: BTreeMap<&'static str, usize>,
}

/// Build rule descriptors for all generated Ascent rules.
///
/// This mirrors the logic in `generate_ascent_source` but instead of generating
/// TokenStream, it builds lightweight descriptors capturing the relation
/// dependencies of each rule.
fn build_rule_descriptors(language: &LanguageDef) -> Vec<RuleDescriptor> {
    let mut descriptors = Vec::new();

    for lang_type in &language.types {
        let cat = &lang_type.name;
        let cat_lower = cat.to_string().to_lowercase();
        let eq_rel = format!("eq_{}", cat_lower);
        let rw_rel = format!("rw_{}", cat_lower);

        // 1. Reflexivity: eq_cat(t, t) <-- cat(t)
        descriptors.push(RuleDescriptor {
            name: format!("reflexivity/{}", cat),
            kind: RuleKind::Reflexivity,
            body_relations: [cat_lower.clone()].into_iter().collect(),
            head_relations: [eq_rel.clone()].into_iter().collect(),
        });

        // 2. Category expansion: cat(c1) <-- cat(c0), rw_cat(c0, c1)
        descriptors.push(RuleDescriptor {
            name: format!("category-expansion/{}", cat),
            kind: RuleKind::CategoryExpansion,
            body_relations: [cat_lower.clone(), rw_rel.clone()].into_iter().collect(),
            head_relations: [cat_lower.clone()].into_iter().collect(),
        });

        // 3. Eq-Rw closure: rw_cat(a, c) <-- eq_cat(a, b), rw_cat(b, c)
        descriptors.push(RuleDescriptor {
            name: format!("eq-rw-closure/{}", cat),
            kind: RuleKind::EqRwClosure,
            body_relations: [eq_rel.clone(), rw_rel.clone()].into_iter().collect(),
            head_relations: [rw_rel.clone()].into_iter().collect(),
        });
    }

    // 4. Eq congruence rules: group by (category, field_types)
    for lang_type in &language.types {
        let cat = &lang_type.name;
        let cat_lower = cat.to_string().to_lowercase();
        let eq_rel = format!("eq_{}", cat_lower);

        // Find constructors for this category with non-terminal args
        let constructors_with_args: Vec<&crate::ast::grammar::GrammarRule> = language
            .terms
            .iter()
            .filter(|r| {
                r.category == *cat
                    && r.bindings.is_empty()
                    && !r.items.iter().any(|i| matches!(i, GrammarItem::Collection { .. }))
            })
            .collect();

        // Collect unique field type sets
        let mut seen_field_sigs: HashSet<Vec<String>> = HashSet::new();
        for rule in &constructors_with_args {
            let arg_cats: Vec<String> = rule
                .items
                .iter()
                .filter_map(|item| {
                    if let GrammarItem::NonTerminal(c) = item {
                        Some(c.to_string())
                    } else {
                        None
                    }
                })
                .collect();

            if arg_cats.is_empty()
                || arg_cats.iter().any(|c| c == "Var" || c == "Integer")
            {
                continue;
            }

            if seen_field_sigs.insert(arg_cats.clone()) {
                let mut body = BTreeSet::new();
                body.insert(cat_lower.clone());
                for fld_cat in &arg_cats {
                    body.insert(format!("eq_{}", fld_cat.to_lowercase()));
                }

                descriptors.push(RuleDescriptor {
                    name: format!(
                        "eq-congruence/{}/{}",
                        cat,
                        arg_cats.join(",")
                    ),
                    kind: RuleKind::EqCongruence,
                    body_relations: body,
                    head_relations: [eq_rel.clone()].into_iter().collect(),
                });
            }
        }
    }

    // 5. User-defined equation rules
    for eq in &language.equations {
        let category = eq
            .left
            .category(language)
            .or_else(|| eq.right.category(language));

        if let Some(cat) = category {
            let cat_lower = cat.to_string().to_lowercase();
            let eq_rel = format!("eq_{}", cat_lower);

            descriptors.push(RuleDescriptor {
                name: format!("user-equation/{}", eq.name),
                kind: RuleKind::UserEquation,
                body_relations: [cat_lower.clone()].into_iter().collect(),
                head_relations: [eq_rel, cat_lower].into_iter().collect(),
            });
        }
    }

    // 6. Base rewrite rules
    for rw in &language.rewrites {
        if rw.is_congruence_rule() {
            continue;
        }

        if let Some(cat) = rw.left.category(language) {
            let cat_lower = cat.to_string().to_lowercase();
            let eq_rel = format!("eq_{}", cat_lower);
            let rw_rel = format!("rw_{}", cat_lower);

            // Base rewrites read eq_cat (via equation matching)
            let mut body = BTreeSet::new();
            body.insert(eq_rel);

            // Also check for EnvQuery relations in premises
            for premise in &rw.premises {
                if let crate::ast::language::Premise::RelationQuery { relation, .. } = premise {
                    body.insert(relation.to_string());
                }
            }

            descriptors.push(RuleDescriptor {
                name: format!("base-rewrite/{}", rw.name),
                kind: RuleKind::BaseRewrite,
                body_relations: body,
                head_relations: [rw_rel].into_iter().collect(),
            });
        }
    }

    // 7. Explicit congruence rewrites
    for rw in &language.rewrites {
        if !rw.is_congruence_rule() {
            continue;
        }

        if let Some(cat) = rw
            .left
            .category(language)
            .or_else(|| rw.right.category(language))
        {
            let cat_lower = cat.to_string().to_lowercase();
            let rw_rel = format!("rw_{}", cat_lower);

            let mut body = BTreeSet::new();
            body.insert(cat_lower);

            // The congruence premise references rw_field_cat
            if let Some((source, _target)) = rw.congruence_premise() {
                // Determine field category from the source variable's context
                // The source var appears in the LHS pattern; its category is the
                // field type that the congruence rewrites through.
                if let Some(field_cat) = rw.left.category(language) {
                    // For congruence rules, the source variable's type determines
                    // the rw relation we join on. Since we don't have direct access
                    // to the field type from here, we use a conservative approach:
                    // look up what category the source variable should be.
                    let source_str = source.to_string();
                    // The congruence reads rw_<source_category>
                    // We need to find which category the premise variable belongs to
                    // by examining the grammar rule for the LHS constructor
                    if let Some(field_cat_name) =
                        find_congruence_field_category(&rw.left, &source_str, language)
                    {
                        body.insert(format!(
                            "rw_{}",
                            field_cat_name.to_lowercase()
                        ));
                    } else {
                        // Conservative: add rw_<same_cat> as fallback
                        body.insert(format!(
                            "rw_{}",
                            field_cat.to_string().to_lowercase()
                        ));
                    }
                }
            }

            descriptors.push(RuleDescriptor {
                name: format!("explicit-congruence/{}", rw.name),
                kind: RuleKind::ExplicitCongruence,
                body_relations: body,
                head_relations: [rw_rel].into_iter().collect(),
            });
        }
    }

    // 8. HOL step rules (rust_code constructors in step mode)
    for rule in &language.terms {
        if rule.rust_code.is_none() {
            continue;
        }
        if rule.eval_mode == Some(EvalMode::Fold) {
            continue;
        }

        let cat_lower = rule.category.to_string().to_lowercase();
        let rw_rel = format!("rw_{}", cat_lower);

        let mut body = BTreeSet::new();
        body.insert(cat_lower);

        // HOL step rules join on rw_<field_cat> for each non-terminal arg
        for item in &rule.items {
            if let GrammarItem::NonTerminal(field_cat) = item {
                body.insert(format!(
                    "rw_{}",
                    field_cat.to_string().to_lowercase()
                ));
            }
        }

        descriptors.push(RuleDescriptor {
            name: format!("hol-step/{}", rule.label),
            kind: RuleKind::HolStep,
            body_relations: body,
            head_relations: [rw_rel].into_iter().collect(),
        });
    }

    // 9. Fold rules (rust_code constructors in fold mode)
    for rule in &language.terms {
        if rule.rust_code.is_none() {
            continue;
        }
        if rule.eval_mode != Some(EvalMode::Fold) {
            continue;
        }

        let cat_lower = rule.category.to_string().to_lowercase();
        let fold_rel = format!("fold_{}", cat_lower);

        let mut body = BTreeSet::new();
        body.insert(cat_lower);

        // Fold rules join on fold_<field_cat> for each non-terminal arg
        for item in &rule.items {
            if let GrammarItem::NonTerminal(field_cat) = item {
                body.insert(format!(
                    "fold_{}",
                    field_cat.to_string().to_lowercase()
                ));
            }
        }

        descriptors.push(RuleDescriptor {
            name: format!("fold/{}", rule.label),
            kind: RuleKind::Fold,
            body_relations: body,
            head_relations: [fold_rel].into_iter().collect(),
        });
    }

    // 10. Deconstruction rules: cat(s) -> tgt(field) for each reachable (src, tgt)
    let mut decon_pairs: BTreeSet<(String, String)> = BTreeSet::new();
    for lang_type in &language.types {
        let src = lang_type.name.to_string();
        for rule in &language.terms {
            if rule.category.to_string() != src {
                continue;
            }
            for item in &rule.items {
                match item {
                    GrammarItem::NonTerminal(tgt) => {
                        decon_pairs.insert((src.clone(), tgt.to_string()));
                    }
                    GrammarItem::Collection { element_type, .. } => {
                        decon_pairs.insert((src.clone(), element_type.to_string()));
                    }
                    _ => {}
                }
            }
        }
    }

    for (src, tgt) in &decon_pairs {
        let src_lower = src.to_lowercase();
        let tgt_lower = tgt.to_lowercase();

        descriptors.push(RuleDescriptor {
            name: format!("deconstruction/{}->{}", src, tgt),
            kind: RuleKind::Deconstruction,
            body_relations: [src_lower].into_iter().collect(),
            head_relations: [tgt_lower].into_iter().collect(),
        });
    }

    descriptors
}

/// Determine the category of the field variable in a congruence rewrite's LHS pattern.
///
/// For a congruence rule like `if S ~> T then (Ctor ... S ...) ~> (Ctor ... T ...)`,
/// this finds the category of the field position where `S` appears in the constructor.
fn find_congruence_field_category(
    lhs: &crate::ast::pattern::Pattern,
    source_var: &str,
    language: &LanguageDef,
) -> Option<String> {
    use crate::ast::pattern::{Pattern, PatternTerm};

    match lhs {
        Pattern::Term(PatternTerm::Apply { constructor, args }) => {
            let grammar_rule = language.get_constructor(constructor)?;
            let mut nt_idx = 0;
            for item in &grammar_rule.items {
                match item {
                    GrammarItem::NonTerminal(field_cat) => {
                        if nt_idx < args.len() {
                            if let Pattern::Term(PatternTerm::Var(v)) = &args[nt_idx] {
                                if v.to_string() == source_var {
                                    return Some(field_cat.to_string());
                                }
                            }
                        }
                        nt_idx += 1;
                    }
                    GrammarItem::Collection { element_type, .. } => {
                        // Check if source_var appears in the collection position
                        if nt_idx < args.len() {
                            if let Pattern::Term(PatternTerm::Var(v)) = &args[nt_idx] {
                                if v.to_string() == source_var {
                                    return Some(element_type.to_string());
                                }
                            }
                        }
                        nt_idx += 1;
                    }
                    _ => {}
                }
            }
            None
        }
        _ => None,
    }
}

/// Analyze the rule-relation dependency graph for semi-naive delta guard efficiency.
///
/// This is the core A-RT02 analysis. It builds the dependency graph, computes
/// delta groups, identifies always-active rules, and detects feedback cycles.
fn analyze_delta_guards(language: &LanguageDef) -> DeltaGuardAnalysis {
    let descriptors = build_rule_descriptors(language);
    let total_rules = descriptors.len();

    // Group rules by their body relation signature
    let mut delta_groups: BTreeMap<BTreeSet<String>, Vec<String>> = BTreeMap::new();
    for desc in &descriptors {
        delta_groups
            .entry(desc.body_relations.clone())
            .or_default()
            .push(desc.name.clone());
    }

    // Identify "always-active" rules: those whose body spans >= 3 distinct
    // relation families. A relation family is determined by prefix:
    // cat_* (category), eq_* (equality), rw_* (rewrite), fold_* (fold),
    // *_contains (projection), or custom.
    let always_active_rules: Vec<String> = descriptors
        .iter()
        .filter(|desc| {
            let families: HashSet<&str> = desc
                .body_relations
                .iter()
                .map(|rel| classify_relation_family(rel))
                .collect();
            families.len() >= 3
        })
        .map(|desc| desc.name.clone())
        .collect();

    // Detect feedback relations: relations that appear in both head and body
    // of any single rule (direct self-dependency).
    let mut feedback_relations = BTreeSet::new();
    for desc in &descriptors {
        for rel in &desc.head_relations {
            if desc.body_relations.contains(rel) {
                feedback_relations.insert(rel.clone());
            }
        }
    }

    // Count distinct relation families across all rules
    let mut all_families: HashSet<&str> = HashSet::new();
    for desc in &descriptors {
        for rel in desc.body_relations.iter().chain(desc.head_relations.iter()) {
            all_families.insert(classify_relation_family(rel));
        }
    }

    // Per-rule-kind breakdown
    let mut rule_kind_counts: BTreeMap<&'static str, usize> = BTreeMap::new();
    for desc in &descriptors {
        *rule_kind_counts.entry(desc.kind.label()).or_insert(0) += 1;
    }

    DeltaGuardAnalysis {
        total_rules,
        delta_groups,
        always_active_rules,
        feedback_relations,
        relation_family_count: all_families.len(),
        rule_kind_counts,
    }
}

/// Classify a relation name into its family for delta group analysis.
///
/// Families:
/// - `"cat"` — category relations (e.g., `proc`, `name`, `int`)
/// - `"eq"` — equality relations (e.g., `eq_proc`)
/// - `"rw"` — rewrite relations (e.g., `rw_proc`)
/// - `"fold"` — fold relations (e.g., `fold_int`)
/// - `"projection"` — collection projections (e.g., `ppar_contains`)
/// - `"custom"` — user-defined relations
fn classify_relation_family(rel: &str) -> &str {
    if rel.starts_with("eq_") {
        "eq"
    } else if rel.starts_with("rw_") {
        "rw"
    } else if rel.starts_with("fold_") {
        "fold"
    } else if rel.ends_with("_contains") {
        "projection"
    } else if rel == "step_term" {
        "custom"
    } else {
        // Bare category names (e.g., "proc", "name") are in the "cat" family
        "cat"
    }
}

/// A-RT02: Emit compile-time lint diagnostics for semi-naive delta guard analysis.
///
/// Analyzes the rule-relation dependency graph of the generated Ascent program and
/// emits informational diagnostics about the fixpoint iteration structure:
///
/// - **G39 (note)**: Summary of delta groups, feedback relations, and always-active rules.
///   Helps users understand which rules drive the fixpoint and where Ascent's built-in
///   semi-naive evaluation is most/least effective.
///
/// - **G40 (note)**: Emitted for each rule with >= 3 body relation families. These rules
///   are "always-active" — they must be checked every iteration because at least one of
///   their body relations is likely to have new tuples.
fn emit_delta_guard_lints(language: &LanguageDef, grammar_name: &str) {
    if language.types.is_empty() {
        return;
    }

    let analysis = analyze_delta_guards(language);

    if analysis.total_rules == 0 {
        return;
    }

    let mut diagnostics = Vec::new();

    // G39: Summary diagnostic — delta group structure
    let singleton_groups = analysis
        .delta_groups
        .values()
        .filter(|rules| rules.len() == 1)
        .count();
    let multi_groups = analysis.delta_groups.len() - singleton_groups;
    let largest_group = analysis
        .delta_groups
        .values()
        .map(|rules| rules.len())
        .max()
        .unwrap_or(0);

    // Build a compact summary of the multi-rule delta groups
    let mut group_summaries = Vec::new();
    for (body_sig, rules) in &analysis.delta_groups {
        if rules.len() > 1 {
            group_summaries.push(format!(
                "  [{} rules] body={{{}}}",
                rules.len(),
                body_sig.iter().cloned().collect::<Vec<_>>().join(", "),
            ));
        }
    }

    let feedback_str = if analysis.feedback_relations.is_empty() {
        "none".to_string()
    } else {
        analysis
            .feedback_relations
            .iter()
            .cloned()
            .collect::<Vec<_>>()
            .join(", ")
    };

    // Per-kind breakdown string
    let kind_breakdown: String = analysis
        .rule_kind_counts
        .iter()
        .map(|(kind, count)| format!("{}:{}", kind, count))
        .collect::<Vec<_>>()
        .join(", ");

    let mut message = format!(
        "A-RT02 delta guard analysis: {} rules [{}], {} delta group(s) \
         ({} singleton, {} multi-rule, largest group: {} rules), \
         {} relation families, feedback relations: {}",
        analysis.total_rules,
        kind_breakdown,
        analysis.delta_groups.len(),
        singleton_groups,
        multi_groups,
        largest_group,
        analysis.relation_family_count,
        feedback_str,
    );

    // Append multi-rule group details
    if !group_summaries.is_empty() {
        if std::env::var("PRATTAIL_LINT_VERBOSE").is_ok() {
            message.push_str("\nmulti-rule delta groups (rules sharing identical body relations):\n");
            message.push_str(&group_summaries.join("\n"));
        } else {
            message.push_str(&format!("\n{} multi-rule delta group(s) (set PRATTAIL_LINT_VERBOSE=1 for details)", group_summaries.len()));
        }
    }

    let hint = if analysis.always_active_rules.is_empty() && analysis.feedback_relations.is_empty()
    {
        "all rules have narrow body dependencies — Ascent's semi-naive evaluation \
         handles them efficiently"
            .to_string()
    } else if !analysis.feedback_relations.is_empty() {
        format!(
            "feedback relation(s) [{}] create self-dependency cycles; \
             these drive the fixpoint iteration until convergence",
            feedback_str,
        )
    } else {
        format!(
            "{} always-active rule(s) span multiple relation families; \
             these rules must be checked every iteration",
            analysis.always_active_rules.len(),
        )
    };

    diagnostics.push(build_lint(
        "G39",
        "semi-naive-delta-groups",
        mettail_prattail::lint::LintSeverity::Note,
        message,
        Some(hint),
        Some(grammar_name.to_string()),
    ));

    // G40: Per-rule detail for always-active rules
    for rule_name in &analysis.always_active_rules {
        diagnostics.push(build_lint(
            "G40",
            "always-active-rule",
            mettail_prattail::lint::LintSeverity::Note,
            format!(
                "rule `{}` is always-active (body spans 3+ relation families) — \
                 cannot benefit from delta guard skipping",
                rule_name,
            ),
            Some(
                "this rule must be evaluated every fixpoint iteration because its \
                 body relations span multiple independent families (cat/eq/rw/fold); \
                 consider whether the rule can be split or simplified"
                    .to_string(),
            ),
            Some(grammar_name.to_string()),
        ));
    }

    emit_collected_diagnostics(diagnostics);
}

/// Format Ascent source for display and file output
fn format_ascent_source(
    theory_name: &str,
    source_name: &Ident,
    relations: &TokenStream,
    category_rules: &TokenStream,
    equation_rules: &TokenStream,
    rewrite_rules: &TokenStream,
    custom_logic: &TokenStream,
) -> String {
    let mut output = String::new();

    output.push_str(&format!("// Generated Ascent Datalog for {} theory\n", theory_name));
    output.push_str("// This file is generated by the theory! macro and is for inspection only.\n");
    output.push_str("// Do not edit manually - changes will be overwritten.\n\n");

    output.push_str("ascent_source! {\n");
    output.push_str(&format!("    {}:\n\n", source_name));

    let relations_str = relations.to_string();
    let category_str = category_rules.to_string();
    let equation_str = equation_rules.to_string();
    let rewrite_str = rewrite_rules.to_string();

    output.push_str("    // Relations\n");
    for line in split_at_top_level(&relations_str, ';') {
        output.push_str(&print_rule(line));
    }

    output.push_str("\n    // Category rules\n");
    for line in split_at_top_level(&category_str, ';') {
        output.push_str(&print_rule(line));
    }

    output.push_str("\n    // Equation rules\n");
    for line in split_at_top_level(&equation_str, ';') {
        output.push_str(&print_rule(line));
    }

    output.push_str("\n    // Rewrite rules\n");
    for line in split_at_top_level(&rewrite_str, ';') {
        output.push_str(&print_rule(line));
    }

    // Custom logic (user-defined relations and rules)
    let custom_str = custom_logic.to_string();
    if !custom_str.trim().is_empty() {
        output.push_str("\n    // Custom logic\n");
        for line in split_at_top_level(&custom_str, ';') {
            output.push_str(&print_rule(line));
        }
    }

    output.push_str("}\n");

    // Apply cosmetic spacing fixes from TokenStream::to_string()
    cleanup_token_spacing(&mut output);

    output
}

/// Generate rewrite rules: base rewrites + explicit congruence rules
///
/// - **Base rewrites**: Rules without premises (S => T)
/// - **Explicit congruences**: Rules with premises (if S => T then LHS => RHS)
///
/// Note: Beta-reduction is NOT generated as rewrite rules. Instead, it happens
/// immediately via `normalize()` when terms are created. This makes beta-reduction
/// "invisible" - users don't see it as a separate reduction step.
///
/// Note: Rewrite congruences are NOT auto-generated. Users explicitly control
/// where rewrites propagate by writing `if S => T then ...` rules.
///
/// When `cat_filter` is `Some`, only generates rules for categories in the filter set.
/// When `analysis` is `Some`, dead constructors are skipped (Sprint 1 DCE).
/// ## ART06 Extended Demand Filtering
///
/// The `demanded` set specifies categories referenced by at least one rule.
/// Rewrite rules and equation-rewrite closure for categories NOT in the demanded
/// set are skipped (their rw_cat and eq_cat relations are not declared).
pub fn generate_rewrite_rules(
    language: &LanguageDef,
    cat_filter: CategoryFilter,
    analysis: Option<&mettail_prattail::PipelineAnalysis>,
    emit_diagnostics: bool,
    demanded: &BTreeSet<String>,
) -> TokenStream {
    let mut rules = Vec::new();

    // Generate base rewrite clauses (no premise)
    let base_rewrite_clauses = generate_base_rewrites(language, cat_filter);
    rules.extend(base_rewrite_clauses);

    // Generate small-step rules for HOL rust_code (step mode)
    let hol_step_rules = generate_hol_step_rules(language, cat_filter, analysis);
    rules.extend(hol_step_rules);

    // Generate big-step fold rules (one rewrite per fold-mode constructor)
    let fold_rules = generate_fold_big_step_rules(language, cat_filter);
    rules.extend(fold_rules);

    // Generate explicit congruence rules (with premise: if S => T then ...)
    // These are user-declared rules that control where rewrites propagate
    let congruence_rules = generate_all_explicit_congruences(language, cat_filter, emit_diagnostics);
    rules.extend(congruence_rules);

    // Equation-rewrite closure: if a is equation-equivalent to b and b rewrites
    // to c, then a also rewrites to c. Needed because congruence rules match
    // `proc(lhs)` directly rather than through `eq_cat(s_orig, s)`.
    // When eq only has reflexive entries this is a no-op.
    // ART06: Skip categories not in the demanded set (no eq_cat/rw_cat relations).
    for lang_type in &language.types {
        if !in_cat_filter(&lang_type.name, cat_filter) {
            continue;
        }
        if !demanded.contains(&lang_type.name.to_string()) {
            continue;
        }
        let rn = common::relation_names(&lang_type.name);
        let eq_rel = &rn.eq_rel;
        let rw_rel = &rn.rw_rel;
        rules.push(quote! {
            #rw_rel(a.clone(), c.clone()) <-- #eq_rel(a, b), #rw_rel(b.clone(), c);
        });
    }

    quote! {
        #(#rules)*
    }
}

/// Generate pre-stratum content for ground HOL step rule optimization.
///
/// The pre-stratum evaluates provably-ground HOL step rules (matching only literal
/// arguments and producing only literal results) in a separate Ascent struct before
/// the main fixpoint. This converges in O(depth) iterations because:
/// - Deconstruction discovers all sub-terms of the initial term
/// - Ground step rules fire on sub-terms with literal children
/// - Category expansion adds newly created literals to the term set
/// - No recursive rules (equations, congruence, user rewrites) are present
///
/// Returns `None` if no ground HOL step rules exist (nothing to pre-compute).
///
/// The main fixpoint retains all rules (including ground ones) for correctness
/// with new terms created by congruence and user-defined rewrites during fixpoint.
fn generate_pre_stratum_content(
    language: &LanguageDef,
    analysis: Option<&mettail_prattail::PipelineAnalysis>,
) -> Option<TokenStream> {
    let strata = common::classify_rewrite_strata(language, analysis);

    // Check if any ground rules exist
    let has_ground = strata
        .values()
        .any(|s| *s == common::RewriteStratum::Ground);
    if !has_ground {
        return None;
    }

    // Collect categories involved in ground rules (for filtering)
    let mut ground_categories = BTreeSet::new();
    for rule in &language.terms {
        let label = rule.label.to_string();
        if strata.get(&label) == Some(&common::RewriteStratum::Ground) {
            ground_categories.insert(rule.category.to_string());
            // Also include argument categories for cross-category rules
            if let Some(ref ctx) = rule.term_context {
                for param in ctx {
                    if let TermParam::Simple { ty, .. } = param {
                        if let crate::ast::types::TypeExpr::Base(cat) = ty {
                            ground_categories.insert(cat.to_string());
                        }
                    }
                }
            }
        }
    }

    // Relations: same as full struct (Ascent requires matching declarations).
    // Pre-stratum needs all categories for relation compatibility, so pass all as demanded.
    let all_cats: BTreeSet<String> = language.types.iter().map(|t| t.name.to_string()).collect();
    let relations = generate_relations(language, &all_cats);

    // Category deconstruction rules: discover sub-terms of the initial term
    let category_rules = generate_category_rules(language, None);

    // Ground HOL step rules only
    let ground_hol_rules = generate_ground_hol_step_rules(language, None, analysis, &strata);

    // Category expansion: cat(c1) <-- cat(c0), rw_cat(c0, c1)
    // This adds newly created literals to the term set so further ground rules can fire.
    let mut expansion_rules = Vec::new();
    for lang_type in &language.types {
        let rn = common::relation_names(&lang_type.name);
        let cat_lower = &rn.cat_lower;
        let rw_rel = &rn.rw_rel;
        expansion_rules.push(quote! {
            #cat_lower(c1.clone()) <-- #cat_lower(c0), #rw_rel(c0, c1);
        });
    }
    let expansion = quote! { #(#expansion_rules)* };

    // Reflexivity rules for eq relations (needed because some rules may reference eq_*)
    let reflexivity = equations::generate_equation_rules_reflexivity_only(language, None, &all_cats);

    Some(quote! {
        #relations

        #category_rules

        #reflexivity

        #ground_hol_rules

        #expansion
    })
}

/// Generate only ground HOL step rules (used by pre-stratum).
///
/// Filters `generate_hol_step_rules` to include only rules classified as Ground
/// by `classify_rewrite_strata`. The output is a subset of what `generate_hol_step_rules`
/// produces, maintaining identical rule structure.
fn generate_ground_hol_step_rules(
    language: &LanguageDef,
    cat_filter: CategoryFilter,
    analysis: Option<&mettail_prattail::PipelineAnalysis>,
    strata: &std::collections::HashMap<String, common::RewriteStratum>,
) -> TokenStream {
    let mut rules = Vec::new();

    for rule in &language.terms {
        let label = rule.label.to_string();

        // Only include ground rules
        if strata.get(&label) != Some(&common::RewriteStratum::Ground) {
            continue;
        }

        if rule.rust_code.is_none() {
            continue;
        }
        if rule.eval_mode == Some(EvalMode::Fold) {
            continue;
        }
        // Sprint 1 DCE: skip dead rules
        if let Some(ref a) = analysis {
            if a.dead_rule_labels.contains(&label) {
                continue;
            }
        }

        let non_terminal_count = rule
            .items
            .iter()
            .filter(|item| matches!(item, GrammarItem::NonTerminal(_)))
            .count();
        if non_terminal_count == 0 {
            continue;
        }

        let category = &rule.category;
        if !in_cat_filter(category, cat_filter) {
            continue;
        }
        if common::native_type_for(language, category).is_none() {
            continue;
        }

        let rn = common::relation_names(category);
        let rw_rel = &rn.rw_rel;
        let cat_rel = &rn.cat_lower;
        let rule_label = &rule.label;
        let result_lit_label = common::literal_label_for(language, category)
            .expect("native category must have literal label");
        let rust_code = &rule.rust_code.as_ref().expect("checked above").code;

        match non_terminal_count {
            2 => {
                let arg_labels = if let Some(ref term_ctx) = rule.term_context {
                    let simple: Vec<_> = term_ctx
                        .iter()
                        .filter_map(|p| match p {
                            TermParam::Simple { ty, .. } => Some(ty),
                            _ => None,
                        })
                        .collect();
                    if let (Some(TypeExpr::Base(left_ty)), Some(TypeExpr::Base(right_ty))) =
                        (simple.first(), simple.get(1))
                    {
                        let left_lit = common::literal_label_for(language, left_ty);
                        let right_lit = common::literal_label_for(language, right_ty);
                        match (left_lit, right_lit) {
                            (Some(ll), Some(rl)) => Some((left_ty.clone(), ll, right_ty.clone(), rl)),
                            _ => None,
                        }
                    } else {
                        None
                    }
                } else {
                    None
                };

                let (left_cat, left_lit_label, right_cat, right_lit_label) = match arg_labels {
                    Some((lc, ll, rc, rl)) => (lc, ll, rc, rl),
                    None => (
                        category.clone(),
                        result_lit_label.clone(),
                        category.clone(),
                        result_lit_label.clone(),
                    ),
                };

                rules.push(quote! {
                    #rw_rel(s.clone(), t) <--
                        #cat_rel(s),
                        if let #category::#rule_label(left, right) = s,
                        if let #left_cat::#left_lit_label(a_ref) = left.as_ref(),
                        if let #right_cat::#right_lit_label(b_ref) = right.as_ref(),
                        let a = a_ref.clone(),
                        let b = b_ref.clone(),
                        let t = #category::#result_lit_label((#rust_code));
                });
            },
            1 => {
                let Some(ref term_context) = rule.term_context else { continue };
                let [TermParam::Simple { name: param_name, ty: ref param_ty }] =
                    term_context.as_slice()
                else { continue };
                let TypeExpr::Base(arg_category) = param_ty else { continue };
                let Some(arg_lit_label) = common::literal_label_for(language, arg_category) else { continue };

                let term_var = format_ident!("orig");
                rules.push(quote! {
                    #rw_rel(#term_var.clone(), t) <--
                        #cat_rel(#term_var),
                        if let #category::#rule_label(inner) = #term_var,
                        if let #arg_category::#arg_lit_label(s_ref) = inner.as_ref(),
                        let #param_name = s_ref.clone(),
                        let t = #category::#result_lit_label((#rust_code));
                });
            },
            _ => {
                let Some(ref term_context) = rule.term_context else { continue };
                let simple_params: Vec<_> = term_context
                    .iter()
                    .filter_map(|p| match p {
                        TermParam::Simple { name, ty } => {
                            if let TypeExpr::Base(base_ty) = ty {
                                Some((name.clone(), base_ty.clone()))
                            } else {
                                None
                            }
                        },
                        _ => None,
                    })
                    .collect();
                if simple_params.len() != non_terminal_count { continue }

                let mut arg_infos = Vec::with_capacity(simple_params.len());
                let mut all_resolved = true;
                for (param_name, arg_cat) in &simple_params {
                    if let Some(lit_label) = common::literal_label_for(language, arg_cat) {
                        arg_infos.push((param_name.clone(), arg_cat.clone(), lit_label));
                    } else {
                        all_resolved = false;
                        break;
                    }
                }
                if !all_resolved { continue }

                let field_names: Vec<Ident> = (0..arg_infos.len())
                    .map(|i| format_ident!("f{}", i))
                    .collect();
                let ref_names: Vec<Ident> = (0..arg_infos.len())
                    .map(|i| format_ident!("r{}", i))
                    .collect();

                let destructure_fields: Vec<TokenStream> = arg_infos
                    .iter()
                    .enumerate()
                    .map(|(i, (_, arg_cat, lit_label))| {
                        let fi = &field_names[i];
                        let ri = &ref_names[i];
                        quote! {
                            if let #arg_cat::#lit_label(#ri) = #fi.as_ref(),
                        }
                    })
                    .collect();

                let let_bindings: Vec<TokenStream> = arg_infos
                    .iter()
                    .enumerate()
                    .map(|(i, (param_name, _, _))| {
                        let ri = &ref_names[i];
                        quote! {
                            let #param_name = #ri.clone(),
                        }
                    })
                    .collect();

                rules.push(quote! {
                    #rw_rel(__src.clone(), __dst) <--
                        #cat_rel(__src),
                        if let #category::#rule_label(#(#field_names),*) = __src,
                        #(#destructure_fields)*
                        #(#let_bindings)*
                        let __dst = #category::#result_lit_label((#rust_code));
                });
            },
        }
    }

    quote! { #(#rules)* }
}

/// Generate small-step rewrite rules for terms that have HOL rust_code (step mode).
/// e.g. Up (NumLit a) (NumLit b) => NumLit(2*a + 3*b) when Up has ![2*a + 3*b]
///
/// When `analysis` is `Some`, skips rules whose constructor label is dead
/// (detected by WFST 4-tier analysis). Dead HOL step rules can never fire
/// because the parser will never produce the dead constructor.
fn generate_hol_step_rules(
    language: &LanguageDef,
    cat_filter: CategoryFilter,
    analysis: Option<&mettail_prattail::PipelineAnalysis>,
) -> Vec<TokenStream> {
    let mut rules = Vec::new();

    // Unified single-pass iteration over language.terms with arity dispatch.
    // Collected into separate vecs to preserve output ordering (binary, unary, N-ary).
    // Sprint 3: Each vec stores (weight, rule) tuples for weight-based sorting.
    // Lower weight = more frequent constructor = should be evaluated first.
    let mut binary_rust_rules: Vec<(f64, TokenStream)> = Vec::new();
    let mut unary_rust_rules: Vec<(f64, TokenStream)> = Vec::new();
    let mut nary_rust_rules: Vec<(f64, TokenStream)> = Vec::new();

    for rule in &language.terms {
        if rule.rust_code.is_none() {
            continue;
        }
        // Skip fold-mode: they use big-step rules instead
        if rule.eval_mode == Some(EvalMode::Fold) {
            continue;
        }
        // Sprint 1 DCE: skip rules whose constructor label is dead
        if let Some(ref a) = analysis {
            if a.dead_rule_labels.contains(&rule.label.to_string()) {
                continue;
            }
        }
        let non_terminal_count = rule
            .items
            .iter()
            .filter(|item| matches!(item, GrammarItem::NonTerminal(_)))
            .count();
        if non_terminal_count == 0 {
            continue;
        }
        let category = &rule.category;
        // Skip categories not in the filter
        if !in_cat_filter(category, cat_filter) {
            continue;
        }
        if common::native_type_for(language, category).is_none() {
            continue;
        }

        let rn = common::relation_names(category);
        let rw_rel = &rn.rw_rel;
        let cat_rel = &rn.cat_lower;
        let label = &rule.label;
        let result_lit_label = common::literal_label_for(language, category)
            .expect("native category must have literal label");
        let rust_code = &rule.rust_code.as_ref().unwrap().code;

        // Sprint 3: look up constructor weight for sorting (lower = more frequent = first)
        let rule_weight = analysis
            .and_then(|a| a.constructor_weights.get(&rule.label.to_string()).copied())
            .unwrap_or(f64::INFINITY);

        match non_terminal_count {
            2 => {
                // Binary step rule (e.g. Add (NumLit a) (NumLit b) => NumLit(a + b))
                // Use argument types from term_context when present, so cross-category
                // rules (e.g. Eq . a:Int, b:Int |- ... : Bool) use correct literal patterns.
                let arg_labels = if let Some(ref term_ctx) = rule.term_context {
                    let simple: Vec<_> = term_ctx
                        .iter()
                        .filter_map(|p| match p {
                            TermParam::Simple { ty, .. } => Some(ty),
                            _ => None,
                        })
                        .collect();
                    if let (Some(TypeExpr::Base(left_ty)), Some(TypeExpr::Base(right_ty))) =
                        (simple.first(), simple.get(1))
                    {
                        let left_lit = common::literal_label_for(language, left_ty);
                        let right_lit = common::literal_label_for(language, right_ty);
                        match (left_lit, right_lit) {
                            (Some(ll), Some(rl)) => {
                                Some((left_ty.clone(), ll, right_ty.clone(), rl))
                            },
                            _ => None,
                        }
                    } else {
                        None
                    }
                } else {
                    None
                };

                let (left_cat, left_lit_label, right_cat, right_lit_label) = match arg_labels {
                    Some((lc, ll, rc, rl)) => (lc, ll, rc, rl),
                    None => (
                        category.clone(),
                        result_lit_label.clone(),
                        category.clone(),
                        result_lit_label.clone(),
                    ),
                };

                binary_rust_rules.push((rule_weight, quote! {
                    #rw_rel(s.clone(), t) <--
                        #cat_rel(s),
                        if let #category::#label(left, right) = s,
                        if let #left_cat::#left_lit_label(a_ref) = left.as_ref(),
                        if let #right_cat::#right_lit_label(b_ref) = right.as_ref(),
                        let a = a_ref.clone(),
                        let b = b_ref.clone(),
                        let t = #category::#result_lit_label((#rust_code));
                }));
            },
            1 => {
                // Unary step rule (e.g. Len . s:Str |- "|" s "|" : Int ![s.len() as i32] step)
                let Some(ref term_context) = rule.term_context else {
                    continue;
                };
                let [TermParam::Simple { name: param_name, ty: ref param_ty }] =
                    term_context.as_slice()
                else {
                    continue;
                };
                let TypeExpr::Base(arg_category) = param_ty else {
                    continue;
                };
                let Some(arg_lit_label) = common::literal_label_for(language, arg_category) else {
                    continue;
                };
                // Use a different name for the term so the param (e.g. s) can be bound
                // for rust_code without shadowing
                let term_var = format_ident!("orig");
                unary_rust_rules.push((rule_weight, quote! {
                    #rw_rel(#term_var.clone(), t) <--
                        #cat_rel(#term_var),
                        if let #category::#label(inner) = #term_var,
                        if let #arg_category::#arg_lit_label(s_ref) = inner.as_ref(),
                        let #param_name = s_ref.clone(),
                        let t = #category::#result_lit_label((#rust_code));
                }));
            },
            _ => {
                // N-ary step rule (3+ arguments)
                let Some(ref term_context) = rule.term_context else {
                    continue;
                };
                let simple_params: Vec<_> = term_context
                    .iter()
                    .filter_map(|p| match p {
                        TermParam::Simple { name, ty } => {
                            if let TypeExpr::Base(base_ty) = ty {
                                Some((name.clone(), base_ty.clone()))
                            } else {
                                None
                            }
                        },
                        _ => None,
                    })
                    .collect();
                if simple_params.len() != non_terminal_count {
                    continue;
                }

                let mut arg_infos = Vec::with_capacity(simple_params.len());
                let mut all_resolved = true;
                for (param_name, arg_cat) in &simple_params {
                    if let Some(lit_label) = common::literal_label_for(language, arg_cat) {
                        arg_infos.push((param_name.clone(), arg_cat.clone(), lit_label));
                    } else {
                        all_resolved = false;
                        break;
                    }
                }
                if !all_resolved {
                    continue;
                }

                let field_names: Vec<Ident> = (0..arg_infos.len())
                    .map(|i| format_ident!("f{}", i))
                    .collect();
                let ref_names: Vec<Ident> = (0..arg_infos.len())
                    .map(|i| format_ident!("r{}", i))
                    .collect();

                let destructure_fields: Vec<TokenStream> = arg_infos
                    .iter()
                    .enumerate()
                    .map(|(i, (_, arg_cat, lit_label))| {
                        let fi = &field_names[i];
                        let ri = &ref_names[i];
                        quote! {
                            if let #arg_cat::#lit_label(#ri) = #fi.as_ref(),
                        }
                    })
                    .collect();

                let let_bindings: Vec<TokenStream> = arg_infos
                    .iter()
                    .enumerate()
                    .map(|(i, (param_name, _, _))| {
                        let ri = &ref_names[i];
                        quote! {
                            let #param_name = #ri.clone(),
                        }
                    })
                    .collect();

                // Use __src/__dst to avoid name collisions with user-defined param names
                nary_rust_rules.push((rule_weight, quote! {
                    #rw_rel(__src.clone(), __dst) <--
                        #cat_rel(__src),
                        if let #category::#label(#(#field_names),*) = __src,
                        #(#destructure_fields)*
                        #(#let_bindings)*
                        let __dst = #category::#result_lit_label((#rust_code));
                }));
            },
        }
    }

    // Sprint 3: Sort each group by weight (lower = more frequent = first)
    // for better cache locality and earlier convergence in Ascent evaluation.
    binary_rust_rules.sort_by(|a, b| a.0.total_cmp(&b.0));
    unary_rust_rules.sort_by(|a, b| a.0.total_cmp(&b.0));
    nary_rust_rules.sort_by(|a, b| a.0.total_cmp(&b.0));

    rules.extend(binary_rust_rules.into_iter().map(|(_, r)| r));
    rules.extend(unary_rust_rules.into_iter().map(|(_, r)| r));
    rules.extend(nary_rust_rules.into_iter().map(|(_, r)| r));

    rules
}

// fold_param_names, fold_params_all_same_category, fold_field_count
// moved to common module
use common::{fold_field_count, fold_param_names, fold_params_all_same_category};

/// Generate big-step fold rules for constructors with eval_mode Fold.
/// fold_<cat>(t, v) computes the value term v of t; one rw_<cat>(s, t) step for whole expression.
/// Supports both native categories (fold to literal) and non-native (e.g. Proc with CastInt/Add).
fn generate_fold_big_step_rules(
    language: &LanguageDef,
    cat_filter: CategoryFilter,
) -> Vec<TokenStream> {
    let mut rules = Vec::new();

    for lang_type in &language.types {
        let category = &lang_type.name;

        // Skip categories not in the filter
        if !in_cat_filter(category, cat_filter) {
            continue;
        }

        let has_fold = language
            .terms
            .iter()
            .any(|r| r.category == *category && r.eval_mode == Some(EvalMode::Fold));
        if !has_fold {
            continue;
        }

        let rn = common::relation_names(category);
        let cat_rel = &rn.cat_lower;
        let fold_rel = &rn.fold_rel;
        let rw_rel = &rn.rw_rel;

        let is_native = common::native_type_for(language, category).is_some();

        if is_native {
            // Native category (e.g. Int): fold to literal variant
            let num_lit = common::literal_label_for(language, category)
                .expect("native category must have a literal label");

            rules.push(quote! {
                #fold_rel(t.clone(), t.clone()) <--
                    #cat_rel(t),
                    if let #category::#num_lit(_) = t;
            });

            for rule in &language.terms {
                if rule.category != *category {
                    continue;
                }
                let param_names = fold_param_names(rule);
                let param_count = param_names.len();

                // Support unary (1 param) and binary (2 params) fold rules
                // where all parameters are of the same category as the result.
                // This filters out cross-category rules like Len(Str)->Int.
                if param_count == 0 || param_count > 2 {
                    continue;
                }
                let all_same_category = fold_params_all_same_category(rule, category);
                if !all_same_category {
                    continue;
                }
                let label = &rule.label;

                let res_expr = if let Some(ref rust_block) = rule.rust_code {
                    let rust_code = &rust_block.code;
                    quote! { #category::#num_lit((#rust_code)) }
                } else {
                    continue;
                };

                if param_count == 1 {
                    // Unary fold rule (e.g., Neg)
                    rules.push(quote! {
                        #fold_rel(s.clone(), res) <--
                            #cat_rel(s),
                            if let #category::#label(inner) = s,
                            #fold_rel(inner.as_ref().clone(), iv),
                            if let #category::#num_lit(a_ref) = &iv,
                            let a = a_ref.clone(),
                            let res = #res_expr;
                    });
                } else {
                    // Binary fold rule (e.g., Add, Sub)
                    rules.push(quote! {
                        #fold_rel(s.clone(), res) <--
                            #cat_rel(s),
                            if let #category::#label(left, right) = s,
                            #fold_rel(left.as_ref().clone(), lv),
                            #fold_rel(right.as_ref().clone(), rv),
                            if let #category::#num_lit(a_ref) = &lv,
                            if let #category::#num_lit(b_ref) = &rv,
                            let a = a_ref.clone(),
                            let b = b_ref.clone(),
                            let res = #res_expr;
                    });
                }
            }
        } else {
            // Non-native category (e.g. Proc): identity for non-fold constructors, rust_code for fold

            // Area 6: Consolidated identity rule — one rule per non-native category
            // Replaces N per-constructor identity rules with one inline match
            let identity_arms: Vec<TokenStream> = language
                .terms
                .iter()
                .filter(|r| r.category == *category && r.eval_mode != Some(EvalMode::Fold))
                .map(|rule| {
                    let label = &rule.label;
                    let n = fold_field_count(rule);
                    if n == 0 {
                        quote! { #category::#label => true, }
                    } else {
                        let pat: Vec<TokenStream> = (0..n).map(|_| quote! { _ }).collect();
                        quote! { #category::#label(#(#pat),*) => true, }
                    }
                })
                .collect();

            if !identity_arms.is_empty() {
                rules.push(quote! {
                    #fold_rel(t.clone(), t.clone()) <--
                        #cat_rel(t),
                        if (match t {
                            #(#identity_arms)*
                            _ => false,
                        });
                });
            }

            // fold_C(s, res) for each constructor with rust_code and eval_mode Fold (unary or binary)
            // If the category has an Err variant, only emit when res is not Err (so we don't
            // rewrite e.g. Add(2, *(3)) to error when the right arg hasn't been evaluated yet).
            let err_label = format_ident!("Err");
            let category_has_err = language
                .terms
                .iter()
                .any(|r| r.category == *category && r.label == err_label);
            for rule in &language.terms {
                if rule.category != *category
                    || rule.eval_mode != Some(EvalMode::Fold)
                    || rule.rust_code.is_none()
                {
                    continue;
                }
                let param_names = fold_param_names(rule);
                let label = &rule.label;
                let rust_code = &rule.rust_code.as_ref().unwrap().code;

                // Only emit fold when result is not Err (e.g. Add only rewrites when both args are ints).
                let filter_err = if category_has_err {
                    quote! {
                        ,
                        if (match & res { #category :: #err_label => false , _ => true })
                    }
                } else {
                    quote! {}
                };

                if param_names.len() == 2 {
                    let p0 = &param_names[0];
                    let p1 = &param_names[1];
                    rules.push(quote! {
                        #fold_rel(s.clone(), res) <--
                            #cat_rel(s),
                            if let #category::#label(left, right) = s,
                            #fold_rel(left.as_ref().clone(), lv),
                            #fold_rel(right.as_ref().clone(), rv),
                            let #p0 = lv,
                            let #p1 = rv,
                            let res = (#rust_code)
                            #filter_err;
                    });
                } else if param_names.len() == 1 {
                    let p0 = &param_names[0];
                    rules.push(quote! {
                        #fold_rel(s.clone(), res) <--
                            #cat_rel(s),
                            if let #category::#label(inner) = s,
                            #fold_rel(inner.as_ref().clone(), lv),
                            let #p0 = lv,
                            let res = (#rust_code)
                            #filter_err;
                    });
                }
            }
        }

        // Area 5: Consolidated fold trigger — one rule per category
        // Replaces N per-constructor trigger rules with one inline match
        let trigger_arms: Vec<TokenStream> = language
            .terms
            .iter()
            .filter(|r| r.category == *category && r.eval_mode == Some(EvalMode::Fold))
            .map(|rule| {
                let label = &rule.label;
                let n = fold_field_count(rule);
                if n == 0 {
                    quote! { #category::#label => true, }
                } else {
                    let pat: Vec<TokenStream> = (0..n).map(|_| quote! { _ }).collect();
                    quote! { #category::#label(#(#pat),*) => true, }
                }
            })
            .collect();

        if !trigger_arms.is_empty() {
            rules.push(quote! {
                #rw_rel(s.clone(), t.clone()) <--
                    #cat_rel(s),
                    if (match s {
                        #(#trigger_arms)*
                        _ => false,
                    }),
                    #fold_rel(s, t);
            });
        }
    }

    rules
}

/// Split a string at occurrences of `delimiter` that are at the top level
/// (not nested inside any bracket pair: `()`, `{}`, `[]`).
///
/// This is the generalized replacement for `split_commas_outside_parens` and
/// also handles `;`-splitting for rule boundaries (which previously broke on
/// block expressions containing internal semicolons).
fn split_at_top_level(s: &str, delimiter: char) -> Vec<&str> {
    let mut result = Vec::new();
    let mut depth = 0i32;
    let mut start = 0;

    for (i, ch) in s.char_indices() {
        match ch {
            '(' | '{' | '[' => depth += 1,
            ')' | '}' | ']' => depth = (depth - 1).max(0),
            c if c == delimiter && depth == 0 => {
                result.push(&s[start..i]);
                start = i + 1;
            },
            _ => {},
        }
    }

    if start <= s.len() {
        result.push(&s[start..]);
    }

    result
}

pub fn split_commas_outside_parens(s: &str) -> Vec<&str> {
    split_at_top_level(s, ',')
}

/// Normalize whitespace in a string by replacing all consecutive whitespace
/// (including newlines) with a single space. This fixes formatting issues
/// from TokenStream::to_string() which can insert unwanted line breaks.
fn normalize_whitespace(s: &str) -> String {
    s.split_whitespace().collect::<Vec<_>>().join(" ")
}

pub fn print_rule(line: &str) -> String {
    if line.trim().is_empty() {
        return String::new();
    }

    // Normalize whitespace to fix TokenStream formatting issues
    let normalized = normalize_whitespace(line);

    let (head, body) = normalized
        .split_once("<- -")
        .unwrap_or((normalized.trim(), ""));
    let head_clauses = split_commas_outside_parens(head);
    let (head_last, head_rest) = head_clauses.split_last().unwrap_or((&"", &[]));
    let clauses = split_commas_outside_parens(body);
    let (last, rest) = clauses.split_last().unwrap_or((&"", &[]));
    if !body.trim().is_empty() {
        let mut result = String::new();
        for clause in head_rest {
            result.push_str(&format_long_clause(clause.trim(), ""));
            result.push_str(",\n");
        }
        result.push_str(&format_long_clause(head_last.trim(), ""));
        result.push_str(" <--\n");
        for clause in rest {
            result.push_str("    ");
            result.push_str(&format_long_clause(clause.trim(), "    "));
            result.push_str(",\n");
        }
        result.push_str("    ");
        result.push_str(&format_long_clause(last.trim(), "    "));
        result.push_str(";\n\n");
        result
    } else {
        format!("{};\n\n", normalized.trim())
    }
}

/// Format a match arm that contains a multi-statement block expression.
///
/// Transforms:
///   `Int::MApply(lam, args) => { let mut v = ...; v.push(...); v }`
/// Into:
///   ```text
///   Int::MApply(lam, args) => {
///       let mut v = ...;
///       v.push(...);
///       v
///   }
///   ```
///
/// If the arm does not contain `=> {` or the block body has no semicolons
/// (single expression), the arm is returned as-is.
fn format_block_arm(arm: &str, arm_indent: &str) -> String {
    // Find `=> {` pattern — the block expression start
    let Some(arrow_pos) = arm.find("=> {") else {
        return arm.to_string();
    };

    let block_start = arrow_pos + 3; // position of `{`
    let after_brace = &arm[block_start + 1..];

    // Find matching closing `}`
    let mut depth = 1i32;
    let mut close_pos = None;
    for (i, ch) in after_brace.char_indices() {
        match ch {
            '{' => depth += 1,
            '}' => {
                depth -= 1;
                if depth == 0 {
                    close_pos = Some(i);
                    break;
                }
            },
            _ => {},
        }
    }

    let Some(close_pos) = close_pos else {
        return arm.to_string();
    };

    let block_body = after_brace[..close_pos].trim();
    let after_close = after_brace[close_pos + 1..].trim(); // e.g., empty or trailing ","

    // Only expand if block contains semicolons (multi-statement)
    if !block_body.contains(';') {
        return arm.to_string();
    }

    let stmts = split_at_top_level(block_body, ';');
    let stmt_indent = format!("{}    ", arm_indent);
    let pattern = &arm[..arrow_pos + 2]; // "Pat =>"

    let mut result = String::new();
    result.push_str(pattern);
    result.push_str(" {\n");

    // Detect trailing semicolon: if the last segment (after trim) is empty,
    // the original block body ended with `;` (e.g., `{ a; b; }` splits to
    // ["a", " b", ""]). We must preserve this so the reformatted block has
    // the same Rust semantics (returns `()` rather than the last expression).
    let has_trailing_semi = stmts.last().is_some_and(|s| s.trim().is_empty());
    let non_empty: Vec<&str> = stmts
        .iter()
        .map(|s| s.trim())
        .filter(|s| !s.is_empty())
        .collect();
    for (i, stmt) in non_empty.iter().enumerate() {
        result.push_str(&stmt_indent);
        result.push_str(stmt);
        if i < non_empty.len() - 1 || has_trailing_semi {
            // Statement or trailing-semicolon position — add semicolon back
            result.push(';');
        }
        // Trailing expression (last, no trailing semi) — no semicolon
        result.push('\n');
    }
    result.push_str(arm_indent);
    result.push('}');
    if !after_close.is_empty() {
        result.push_str(after_close);
    }

    result
}

/// Format a clause that may contain long match expressions.
///
/// If the clause is short (< 100 chars) or contains no match, returns it as-is.
/// Otherwise, splits match arms onto separate indented lines for readability.
///
/// `base_indent` is the indentation level of the clause itself (e.g., "    " for body clauses).
fn format_long_clause(clause: &str, base_indent: &str) -> String {
    if clause.len() < 100 || !clause.contains("match ") {
        return clause.to_string();
    }

    // Find each match expression and format it
    let mut result = String::with_capacity(clause.len() * 2);
    let mut remaining = clause;

    while let Some(match_start) = remaining.find("match ") {
        // Emit everything before the match
        result.push_str(&remaining[..match_start]);

        // Find the opening `{` of the match body
        let after_match = &remaining[match_start..];
        let Some(brace_offset) = after_match.find('{') else {
            // No brace found — just emit the rest
            result.push_str(after_match);
            remaining = "";
            break;
        };

        let match_header = &after_match[..brace_offset + 1]; // "match <expr> {"
        let after_brace = &after_match[brace_offset + 1..];

        // Find the matching closing `}`
        let mut depth = 1i32;
        let mut close_pos = None;
        for (i, ch) in after_brace.char_indices() {
            match ch {
                '{' => depth += 1,
                '}' => {
                    depth -= 1;
                    if depth == 0 {
                        close_pos = Some(i);
                        break;
                    }
                },
                _ => {},
            }
        }

        let Some(close_pos) = close_pos else {
            // Unbalanced — just emit the rest
            result.push_str(after_match);
            remaining = "";
            break;
        };

        let match_body = after_brace[..close_pos].trim();
        let after_close = &after_brace[close_pos + 1..]; // e.g., ").into_iter()"

        // Split arms at top-level commas within the match body
        let arms = split_at_top_level(match_body, ',');

        // Only format if there are multiple arms
        if arms.len() <= 1 || match_body.len() < 60 {
            result.push_str(match_header);
            result.push(' ');
            result.push_str(match_body);
            result.push_str(" }");
        } else {
            let arm_indent = format!("{}    ", base_indent);
            result.push_str(match_header);
            result.push('\n');
            for (i, arm) in arms.iter().enumerate() {
                let arm = arm.trim();
                if arm.is_empty() {
                    continue;
                }
                let formatted = format_block_arm(arm, &arm_indent);
                result.push_str(&arm_indent);
                result.push_str(&formatted);
                if i < arms.len() - 1 {
                    result.push(',');
                }
                result.push('\n');
            }
            result.push_str(base_indent);
            result.push('}');
        }

        remaining = after_close;
    }

    // Emit anything after the last match
    result.push_str(remaining);
    result
}

/// Apply cosmetic spacing fixes to the final output.
///
/// TokenStream::to_string() inserts spaces in paths (`Int :: Tern`),
/// macro invocations (`vec! [`, `unreachable! ()`), etc.
fn cleanup_token_spacing(output: &mut String) {
    // Path separators: "Int :: Tern" → "Int::Tern"
    // Must handle both `Foo :: Bar` (type path) and `crate :: eqrel`
    while let Some(pos) = output.find(" :: ") {
        output.replace_range(pos..pos + 4, "::");
    }
    // Macro invocations with brackets: "vec! [" → "vec!["
    while let Some(pos) = output.find("! [") {
        // Verify the char before is alphanumeric (macro name)
        if pos > 0 && output.as_bytes()[pos - 1].is_ascii_alphanumeric() {
            output.replace_range(pos..pos + 3, "![");
        } else {
            // Not a macro — skip by inserting a sentinel and continue
            // Actually, just break to avoid infinite loop — this pattern is rare
            break;
        }
    }
    // Macro invocations with parens: "unreachable! ()" → "unreachable!()"
    while let Some(pos) = output.find("! (") {
        if pos > 0 && output.as_bytes()[pos - 1].is_ascii_alphanumeric() {
            output.replace_range(pos..pos + 3, "!(");
        } else {
            break;
        }
    }
    // Dereference spacing: "(* *" → "(**" (from `(**x0).clone()`)
    while let Some(pos) = output.find("(* *") {
        output.replace_range(pos..pos + 4, "(**");
    }
    // Product type turbofish: ":: < i32 > ()" → "::<i32>()"
    // More generally, fix spacing in turbofish expressions
    while let Some(pos) = output.find(":: < ") {
        // Find the closing " >"
        if let Some(gt_pos) = output[pos + 5..].find(" >") {
            let end = pos + 5 + gt_pos + 2;
            let inner = output[pos + 5..pos + 5 + gt_pos].to_string();
            let replacement = format!("::<{}>", inner);
            output.replace_range(pos..end, &replacement);
        } else {
            break;
        }
    }
    // Reference spacing: "& *" → "&*", "& mut " stays
    // Be careful not to touch "& mut"
    // Pattern: "& * *" → "&**", "& * " → "&*"  (from `&**x`)
    while let Some(pos) = output.find("& * *") {
        output.replace_range(pos..pos + 5, "&**");
    }
    while let Some(pos) = output.find("& *") {
        // Check it's not already handled (no more "& * *" exists)
        output.replace_range(pos..pos + 3, "&*");
    }
    // Remaining "& " before identifiers in ref patterns (from `& s_f0_binder`)
    // Only fix when followed by a non-mut, non-space character — too risky to do generically
    // so we'll leave those for now
}

// ══════════════════════════════════════════════════════════════════════════════
// Property-based tests for pretty-printer string transformations
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    // ── Helpers ──────────────────────────────────────────────────────────────

    /// Extract the non-whitespace characters from a string (preserving order).
    fn non_ws(s: &str) -> Vec<char> {
        s.chars().filter(|c| !c.is_whitespace()).collect()
    }

    /// Count occurrences of `needle` at the top level of `s` (depth 0).
    fn count_top_level(s: &str, needle: char) -> usize {
        let mut depth = 0i32;
        let mut count = 0;
        for ch in s.chars() {
            match ch {
                '(' | '{' | '[' => depth += 1,
                ')' | '}' | ']' => depth = (depth - 1).max(0),
                c if c == needle && depth == 0 => count += 1,
                _ => {},
            }
        }
        count
    }

    // ── Generators ───────────────────────────────────────────────────────────

    /// Strategy for well-bracketed strings suitable for split_at_top_level testing.
    ///
    /// Produces strings where every `(`, `{`, `[` has a matching `)`, `}`, `]`
    /// and brackets are properly nested. May contain `;` at any level.
    fn arb_well_bracketed(max_depth: u32) -> impl Strategy<Value = String> {
        let leaf = prop_oneof!["[a-zA-Z0-9_ ]{0,10}", "[a-zA-Z0-9_ ]*;[a-zA-Z0-9_ ]*",];
        leaf.prop_recursive(max_depth, 256, 4, |inner| {
            prop_oneof![
                (inner.clone(), inner.clone()).prop_map(|(a, b)| format!("{}({})", a, b)),
                (inner.clone(), inner.clone()).prop_map(|(a, b)| format!("{}{{{}}}", a, b)),
                (inner.clone(), inner.clone()).prop_map(|(a, b)| format!("{}[{}]", a, b)),
                (inner.clone(), inner.clone()).prop_map(|(a, b)| format!("{}{}", a, b)),
            ]
        })
    }

    /// Strategy for match arms suitable for format_block_arm testing.
    ///
    /// Produces strings of the form `Pattern => { stmts }` where stmts are
    /// semicolon-separated well-bracketed expressions.
    fn arb_match_arm() -> impl Strategy<Value = String> {
        let stmt = "[a-zA-Z_][a-zA-Z0-9_]{0,15}";
        // 1-5 statements
        prop::collection::vec(stmt, 1..=5).prop_map(|stmts| {
            let body = stmts.join("; ");
            format!("Pat => {{ {} }}", body)
        })
    }

    /// Strategy for match arms that end with a trailing semicolon.
    fn arb_match_arm_trailing_semi() -> impl Strategy<Value = String> {
        let stmt = "[a-zA-Z_][a-zA-Z0-9_]{0,15}";
        prop::collection::vec(stmt, 1..=5).prop_map(|stmts| {
            let body = stmts.join("; ");
            format!("Pat => {{ {}; }}", body)
        })
    }

    // ── Property: P1 — Split-join roundtrip ──────────────────────────────────

    proptest! {
        /// Joining the segments of split_at_top_level with the delimiter
        /// reconstructs the original string exactly.
        #[test]
        fn prop_split_join_roundtrip(
            s in arb_well_bracketed(3),
            delim in prop_oneof![Just(';'), Just(',')],
        ) {
            let parts = split_at_top_level(&s, delim);
            let rejoined: String = parts.join(&delim.to_string());
            prop_assert_eq!(rejoined, s,
                "split_at_top_level roundtrip failed for delimiter {:?}", delim);
        }

        /// Also test with completely arbitrary strings (not just well-bracketed).
        #[test]
        fn prop_split_join_roundtrip_arbitrary(
            s in "[ -~]{0,200}",
            delim in prop_oneof![Just(';'), Just(',')],
        ) {
            let parts = split_at_top_level(&s, delim);
            let rejoined: String = parts.join(&delim.to_string());
            prop_assert_eq!(rejoined, s);
        }
    }

    // ── Property: P2 — Segment count ─────────────────────────────────────────

    proptest! {
        /// The number of segments equals the number of top-level delimiters plus one.
        #[test]
        fn prop_segment_count(
            s in arb_well_bracketed(3),
            delim in prop_oneof![Just(';'), Just(',')],
        ) {
            let parts = split_at_top_level(&s, delim);
            let expected = count_top_level(&s, delim) + 1;
            prop_assert_eq!(parts.len(), expected,
                "segment count mismatch for {:?} with delimiter {:?}", s, delim);
        }
    }

    // ── Property: P3 — No top-level delimiters in segments ───────────────────

    proptest! {
        /// Each segment of split_at_top_level contains zero top-level occurrences
        /// of the delimiter.
        #[test]
        fn prop_no_top_level_delims_in_segments(
            s in arb_well_bracketed(3),
            delim in prop_oneof![Just(';'), Just(',')],
        ) {
            let parts = split_at_top_level(&s, delim);
            for (i, part) in parts.iter().enumerate() {
                let inner_count = count_top_level(part, delim);
                prop_assert_eq!(inner_count, 0,
                    "segment {} ({:?}) contains top-level {:?}", i, part, delim);
            }
        }
    }

    // ── Property: P4 — Token preservation (non-whitespace chars) ─────────────

    proptest! {
        /// format_block_arm preserves all non-whitespace characters in order.
        #[test]
        fn prop_token_preservation(arm in arb_match_arm()) {
            let formatted = format_block_arm(&arm, "    ");
            prop_assert_eq!(non_ws(&formatted), non_ws(&arm),
                "non-whitespace token sequence changed");
        }

        /// Token preservation also holds for arms with trailing semicolons.
        #[test]
        fn prop_token_preservation_trailing_semi(arm in arb_match_arm_trailing_semi()) {
            let formatted = format_block_arm(&arm, "    ");
            prop_assert_eq!(non_ws(&formatted), non_ws(&arm),
                "non-whitespace token sequence changed (trailing semi)");
        }
    }

    // ── Property: P5 — Idempotency ──────────────────────────────────────────

    proptest! {
        /// Applying format_block_arm twice yields the same result as once.
        #[test]
        fn prop_idempotency(arm in arb_match_arm()) {
            let once = format_block_arm(&arm, "    ");
            let twice = format_block_arm(&once, "    ");
            prop_assert_eq!(twice, once, "format_block_arm is not idempotent");
        }

        /// Idempotency also holds for arms with trailing semicolons.
        #[test]
        fn prop_idempotency_trailing_semi(arm in arb_match_arm_trailing_semi()) {
            let once = format_block_arm(&arm, "    ");
            let twice = format_block_arm(&once, "    ");
            prop_assert_eq!(twice, once,
                "format_block_arm is not idempotent (trailing semi)");
        }
    }

    // ── Property: P6 — Semicolon count preservation ─────────────────────────

    proptest! {
        /// format_block_arm preserves the total number of semicolons.
        #[test]
        fn prop_semicolon_count_preservation(arm in arb_match_arm()) {
            let formatted = format_block_arm(&arm, "    ");
            let orig_count = arm.chars().filter(|&c| c == ';').count();
            let fmt_count = formatted.chars().filter(|&c| c == ';').count();
            prop_assert_eq!(fmt_count, orig_count,
                "semicolon count changed: {} → {}", orig_count, fmt_count);
        }

        /// Semicolon count also preserved for trailing-semicolon arms.
        #[test]
        fn prop_semicolon_count_trailing_semi(arm in arb_match_arm_trailing_semi()) {
            let formatted = format_block_arm(&arm, "    ");
            let orig_count = arm.chars().filter(|&c| c == ';').count();
            let fmt_count = formatted.chars().filter(|&c| c == ';').count();
            prop_assert_eq!(fmt_count, orig_count,
                "semicolon count changed (trailing semi): {} → {}", orig_count, fmt_count);
        }
    }

    // ── Property: P7 — Trailing semicolons specifically preserved ────────────

    proptest! {
        /// Arms with trailing semicolons retain the trailing semicolon after formatting.
        #[test]
        fn prop_trailing_semi_preserved(arm in arb_match_arm_trailing_semi()) {
            let formatted = format_block_arm(&arm, "    ");
            // The formatted block should end with `;\n}\n` or `;\n}`
            // (i.e., the last statement line before `}` ends with `;`)
            let trimmed = formatted.trim_end();
            // Find the closing brace
            if let Some(close_pos) = trimmed.rfind('}') {
                let before_close = trimmed[..close_pos].trim_end();
                prop_assert!(before_close.ends_with(';'),
                    "trailing semicolon lost in formatted output: {:?}", formatted);
            }
        }
    }

    // ── Deterministic unit tests ─────────────────────────────────────────────

    #[test]
    fn test_split_at_top_level_basic() {
        assert_eq!(split_at_top_level("a; b; c", ';'), vec!["a", " b", " c"]);
    }

    #[test]
    fn test_split_at_top_level_nested() {
        // Semicolons inside brackets are not split points
        assert_eq!(split_at_top_level("f(a; b); c", ';'), vec!["f(a; b)", " c"]);
    }

    #[test]
    fn test_split_at_top_level_empty_trailing() {
        // Trailing semicolon produces empty trailing segment
        assert_eq!(split_at_top_level("a; b;", ';'), vec!["a", " b", ""]);
    }

    #[test]
    fn test_format_block_arm_no_expansion() {
        // No `=> {` pattern — returned as-is
        let arm = "Pat => expr";
        assert_eq!(format_block_arm(arm, ""), arm);
    }

    #[test]
    fn test_format_block_arm_single_expr() {
        // Single expression (no `;`) — returned as-is
        let arm = "Pat => { expr }";
        assert_eq!(format_block_arm(arm, ""), arm);
    }

    #[test]
    fn test_format_block_arm_multi_stmt() {
        let arm = "Pat => { a; b; c }";
        let formatted = format_block_arm(arm, "");
        assert_eq!(formatted, "Pat => {\n    a;\n    b;\n    c\n}");
    }

    #[test]
    fn test_format_block_arm_trailing_semi() {
        let arm = "Pat => { a; b; }";
        let formatted = format_block_arm(arm, "");
        // Trailing semicolon must be preserved
        assert_eq!(formatted, "Pat => {\n    a;\n    b;\n}");
    }

    #[test]
    fn test_format_block_arm_trailing_semi_token_preservation() {
        let arm = "Pat => { a; b; }";
        let formatted = format_block_arm(arm, "");
        assert_eq!(non_ws(&formatted), non_ws(arm));
    }

    #[test]
    fn test_format_block_arm_idempotent() {
        let arm = "Pat => { a; b; c }";
        let once = format_block_arm(arm, "    ");
        let twice = format_block_arm(&once, "    ");
        assert_eq!(twice, once);
    }

    #[test]
    fn test_format_block_arm_idempotent_trailing_semi() {
        let arm = "Pat => { a; b; }";
        let once = format_block_arm(arm, "    ");
        let twice = format_block_arm(&once, "    ");
        assert_eq!(twice, once);
    }

    // ── A-RT02: Delta Guard Analysis Tests ─────────────────────────────────

    #[test]
    fn test_classify_relation_family() {
        assert_eq!(classify_relation_family("proc"), "cat");
        assert_eq!(classify_relation_family("name"), "cat");
        assert_eq!(classify_relation_family("int"), "cat");
        assert_eq!(classify_relation_family("eq_proc"), "eq");
        assert_eq!(classify_relation_family("eq_name"), "eq");
        assert_eq!(classify_relation_family("rw_proc"), "rw");
        assert_eq!(classify_relation_family("rw_int"), "rw");
        assert_eq!(classify_relation_family("fold_int"), "fold");
        assert_eq!(classify_relation_family("ppar_contains"), "projection");
        assert_eq!(classify_relation_family("step_term"), "custom");
    }

    #[test]
    fn test_rule_kind_labels() {
        assert_eq!(RuleKind::Reflexivity.label(), "reflexivity");
        assert_eq!(RuleKind::EqCongruence.label(), "eq-congruence");
        assert_eq!(RuleKind::UserEquation.label(), "user-equation");
        assert_eq!(RuleKind::BaseRewrite.label(), "base-rewrite");
        assert_eq!(RuleKind::HolStep.label(), "hol-step");
        assert_eq!(RuleKind::Fold.label(), "fold");
        assert_eq!(RuleKind::ExplicitCongruence.label(), "explicit-congruence");
        assert_eq!(RuleKind::EqRwClosure.label(), "eq-rw-closure");
        assert_eq!(RuleKind::CategoryExpansion.label(), "category-expansion");
        assert_eq!(RuleKind::Deconstruction.label(), "deconstruction");
    }

    #[test]
    fn test_rule_descriptor_feedback_detection() {
        // A category-expansion rule reads cat(c0) and writes cat(c1) — same relation
        let desc = RuleDescriptor {
            name: "category-expansion/Proc".to_string(),
            kind: RuleKind::CategoryExpansion,
            body_relations: ["proc".to_string(), "rw_proc".to_string()]
                .into_iter()
                .collect(),
            head_relations: ["proc".to_string()].into_iter().collect(),
        };

        // "proc" appears in both body and head — feedback
        let feedback: BTreeSet<String> = desc
            .head_relations
            .iter()
            .filter(|rel| desc.body_relations.contains(*rel))
            .cloned()
            .collect();

        assert!(feedback.contains("proc"));
        assert_eq!(feedback.len(), 1);
    }

    #[test]
    fn test_always_active_detection() {
        // A rule spanning cat + eq + rw families should be "always-active"
        let desc = RuleDescriptor {
            name: "test-rule".to_string(),
            kind: RuleKind::HolStep,
            body_relations: [
                "proc".to_string(),     // cat family
                "eq_name".to_string(),  // eq family
                "rw_int".to_string(),   // rw family
            ]
            .into_iter()
            .collect(),
            head_relations: ["rw_proc".to_string()].into_iter().collect(),
        };

        let families: HashSet<&str> = desc
            .body_relations
            .iter()
            .map(|rel| classify_relation_family(rel))
            .collect();

        assert_eq!(families.len(), 3);
        assert!(families.contains("cat"));
        assert!(families.contains("eq"));
        assert!(families.contains("rw"));
    }

    #[test]
    fn test_delta_group_signature() {
        // Two rules with identical body relations share a delta group
        let desc1 = RuleDescriptor {
            name: "reflexivity/Proc".to_string(),
            kind: RuleKind::Reflexivity,
            body_relations: ["proc".to_string()].into_iter().collect(),
            head_relations: ["eq_proc".to_string()].into_iter().collect(),
        };

        let desc2 = RuleDescriptor {
            name: "deconstruction/Proc->Name".to_string(),
            kind: RuleKind::Deconstruction,
            body_relations: ["proc".to_string()].into_iter().collect(),
            head_relations: ["name".to_string()].into_iter().collect(),
        };

        // Both read only "proc" — same body signature → same delta group
        assert_eq!(desc1.body_relations, desc2.body_relations);

        // But they write different relations
        assert_ne!(desc1.head_relations, desc2.head_relations);
    }
}
