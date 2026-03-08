//! Unified compile-time lint and diagnostic layer for PraTTaIL grammars.
//!
//! Routes **all** diagnostic output through [`LintDiagnostic`] structs and
//! [`format_diagnostic_colored()`] for consistent, ANSI-colorized, Rust-compiler-style
//! output. No diagnostic bypasses this system.
//!
//! ## Lint Categories
//!
//! | Prefix | Category | Source Data |
//! |--------|----------|-------------|
//! | G | Grammar structure | ParserBundle (pre-WFST) + macros crate |
//! | W | WFST-specific | Prediction WFSTs |
//! | R | Recovery | Recovery WFSTs + RecoveryConfig |
//! | C | Cross-category | Cast rules + FIRST sets |
//! | X | Composition | Composed grammar verification |
//! | P | Performance | DFA stats + WFST metrics |
//! | I | Infrastructure | Pipeline progress, env overrides, I/O |
//!
//! ## Severity Levels
//!
//! | Level | Color | Description |
//! |-------|-------|-------------|
//! | `Info` | Bold cyan | Infrastructure progress — pipeline status |
//! | `Note` | Bold cyan | Informational — no action required |
//! | `Warning` | Bold yellow | Possible issue — review recommended |
//! | `Error` | Bold red | Correctness bug — compilation may fail |
//!
//! ## Macro-Phase Lints
//!
//! The following lints are emitted by the macros crate via [`emit_diagnostic()`]
//! because they require access to equation/rewrite data unavailable in the
//! PraTTaIL pipeline:
//!
//! | ID | Severity | Name | Description |
//! |----|----------|------|-------------|
//! | G25 | note | cancellation-pair-detected | Equation `Outer(Inner(X)) = X` suppressed from eqrel |
//! | G26 | note | equation-subsumed | Equation eliminated by subsumption |
//! | G27 | warning | rule-subsumption-candidate | Rule may be subsumed by more general rule |
//! | G28 | note | alpha-equivalent-groups | Alpha-equivalent LHS pattern groups |
//! | G29 | note | dependency-groups | Fine-grained dependency groups |
//! | G30 | note | isomorphic-wfst-groups | Isomorphic WFST dispatch topology |
//! | G31 | note | subsumed-equations-eliminated | N equations eliminated from codegen |
//! | W09 | warning | cancellation-pair-missing-rewrite | Suppressed equation has no corresponding rewrite |
//! | I10 | warning | ascent-file-write-failed | Ascent Datalog file I/O error |
//!
//! ## Display Format
//!
//! Rust-compiler-style diagnostics to stderr with ANSI colors:
//!
//! ```text
//! error[C01]: cast cycle detected: Int -> Proc -> Int
//!   = hint: break the cycle by removing one cast direction
//!
//! warning[W01]: rule `FloatToStr` in category `Str` is unreachable (dead code)
//!   = hint: remove the rule or add a unique dispatch token
//!
//! info[I01] (Ambient): transducer cascade: 8 change(s) across 3 categories (12 total iterations)
//! ```

use std::collections::{HashMap, HashSet};
use std::fmt;

use crate::SourceLocation;
use crate::binding_power::BindingPowerTable;
use crate::decision_tree::CategoryDecisionTree;
use crate::dispatch::{CastRule, CrossCategoryRule};
use crate::pipeline::CategoryInfo;
use crate::prediction::{FirstSet, FollowSetInput, RuleInfo};
use crate::recovery::{RecoveryConfig, RecoveryWfst};
use crate::recursive::RDRuleInfo;
use crate::token_id::TokenIdMap;
use crate::wfst::PredictionWfst;
use crate::SyntaxItemSpec;

// ══════════════════════════════════════════════════════════════════════════════
// Core types
// ══════════════════════════════════════════════════════════════════════════════

/// Lint severity level.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LintSeverity {
    /// Infrastructure informational — pipeline progress messages.
    Info,
    /// Informational note — no action required.
    Note,
    /// Compile-time warning — possible issue.
    Warning,
    /// Compile-time error — correctness bug.
    Error,
}

impl fmt::Display for LintSeverity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LintSeverity::Info => write!(f, "info"),
            LintSeverity::Note => write!(f, "note"),
            LintSeverity::Warning => write!(f, "warning"),
            LintSeverity::Error => write!(f, "error"),
        }
    }
}

/// A structured lint diagnostic.
#[derive(Debug, Clone)]
pub struct LintDiagnostic {
    /// Lint ID (e.g., "G01", "W01", "C01").
    pub id: &'static str,
    /// Human-readable lint name (e.g., "left-recursion", "dead-rule").
    pub name: &'static str,
    /// Severity level.
    pub severity: LintSeverity,
    /// Category name (for category-specific lints).
    pub category: Option<String>,
    /// Rule label (for rule-specific lints).
    pub rule: Option<String>,
    /// Diagnostic message.
    pub message: String,
    /// Optional fix suggestion.
    pub hint: Option<String>,
    /// Grammar name for multi-grammar context.
    pub grammar_name: Option<String>,
    /// Source location of the relevant rule in the `language!` macro.
    pub source_location: Option<SourceLocation>,
}

impl fmt::Display for LintDiagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}[{}]: {}", self.severity, self.id, self.message)?;
        // Source location line (rustc-style `-->` pointer)
        if let Some(ref loc) = self.source_location {
            if loc.line > 0 {
                write!(f, "\n  --> <macro>:{}", loc)?;
            }
        }
        // Category/rule context line
        match (&self.category, &self.rule) {
            (Some(cat), Some(rule)) => {
                write!(f, "\n  = in category `{}`, rule `{}`", cat, rule)?;
            }
            (Some(cat), None) => {
                write!(f, "\n  = in category `{}`", cat)?;
            }
            _ => {}
        }
        if let Some(ref hint) = self.hint {
            write!(f, "\n  = hint: {}", hint)?;
        }
        Ok(())
    }
}

/// All pipeline data available for linting (borrows, no copies).
pub struct LintContext<'a> {
    /// Grammar name (e.g., "RhoPi").
    pub grammar_name: &'a str,
    /// Rule source locations: (label, category) → SourceLocation.
    pub rule_locations: &'a HashMap<(String, String), SourceLocation>,
    /// Category metadata.
    pub categories: &'a [CategoryInfo],
    /// Rule analysis info (from prediction analysis).
    pub rules: &'a [RuleInfo],
    /// RD rule info (recursive-descent handler data).
    pub rd_rules: &'a [RDRuleInfo],
    /// FIRST sets per category.
    pub first_sets: &'a HashMap<String, FirstSet>,
    /// FOLLOW sets per category.
    pub follow_sets: &'a HashMap<String, FirstSet>,
    /// Binding power table.
    pub bp_table: &'a BindingPowerTable,
    /// Prediction WFSTs per category.
    pub prediction_wfsts: &'a HashMap<String, PredictionWfst>,
    /// Recovery WFSTs (one per category).
    pub recovery_wfsts: &'a [RecoveryWfst],
    /// Cast rules.
    pub cast_rules: &'a [CastRule],
    /// Cross-category rules.
    pub cross_rules: &'a [CrossCategoryRule],
    /// Categories needing NFA spillover buffers.
    pub nfa_spillover_categories: &'a HashSet<String>,
    /// Recovery configuration (19 fields).
    pub recovery_config: &'a RecoveryConfig,
    /// All syntax per rule: (label, category, syntax).
    pub all_syntax: &'a [(String, String, Vec<SyntaxItemSpec>)],
    /// FOLLOW set inputs (for terminal extraction).
    pub follow_inputs: &'a [FollowSetInput],
    /// Dependency groups from equations/rewrites/logic for transitive liveness analysis.
    pub semantic_dependency_groups: &'a [HashSet<String>],
    /// Pre-collected diagnostics from pipeline phases that emit before lint context
    /// is constructed (e.g., W05 from composed dispatch resolution).
    pub pre_collected_diagnostics: &'a [LintDiagnostic],
    /// Decision trees per category (from PathMap trie construction).
    pub decision_trees: &'a HashMap<String, CategoryDecisionTree>,
    /// Token ID mapping for dispatch_strategy() queries.
    pub token_id_map: &'a TokenIdMap,
    /// Pre-computed dead-rule warnings from the pipeline's 2nd
    /// `collect_dead_rule_labels` pass (after decision tree construction).
    /// `lint_w01_dead_rule` reads these instead of re-invoking `detect_dead_rules`.
    pub dead_rule_warnings: &'a [crate::pipeline::DeadRuleWarning],
    /// Grammar profile for severity modulation.
    pub grammar_profile: Option<&'a crate::cost_benefit::GrammarProfile>,
    /// WPDS analysis results (stack-aware reachability).
    /// `None` if WPDS analysis was not run (G25 gate disabled or < 2 categories).
    pub wpds_analysis: Option<&'a crate::wpds::WpdsAnalysis>,
    /// P05: Wall-clock time spent in WPDS analysis (set by pipeline).
    pub wpds_elapsed: Option<std::time::Duration>,

    // ── Mathematical analysis results ──────────────────────────────────────

    /// Safety verification result (always-on when WPDS runs).
    pub safety_result: Option<&'a crate::verify::SafetyResult<crate::automata::semiring::BooleanWeight>>,
    /// CEGAR verification result (always-on when WPDS runs).
    pub cegar_result: Option<&'a crate::cegar::CegarLog>,
    /// Algebraic program analysis (Tarjan path expressions).
    pub algebraic_result: Option<&'a crate::algebraic::AlgebraicSummary>,
    /// P06: Wall-clock time spent in mathematical analysis phase.
    pub math_analysis_elapsed: Option<std::time::Duration>,

    /// Confluence analysis (TRS critical pairs).
    #[cfg(feature = "trs-analysis")]
    pub confluence_result: Option<&'a crate::confluence::ConfluenceAnalysis>,
    /// Termination analysis (dependency pairs).
    #[cfg(feature = "trs-analysis")]
    pub termination_result: Option<&'a crate::termination::TerminationResult>,
    /// VPA analysis (structured sublanguage).
    #[cfg(feature = "vpa")]
    pub vpa_result: Option<&'a crate::vpa::VpaAnalysis>,
    /// Weighted tree automaton analysis.
    #[cfg(feature = "tree-automata")]
    pub wta_result: Option<&'a crate::tree_automaton::WtaAnalysis>,
    /// EWPDS merge site analysis.
    #[cfg(feature = "wpds-extended")]
    pub ewpds_result: Option<&'a crate::ewpds::EwpdsAnalysis>,
    /// ARA affine-relation analysis.
    #[cfg(feature = "wpds-ara")]
    pub ara_result: Option<&'a crate::ara::AraAnalysis>,
    /// Petri net analysis.
    #[cfg(feature = "petri")]
    pub petri_result: Option<&'a crate::petri::PetriAnalysis>,
    /// Nominal automaton analysis.
    #[cfg(feature = "nominal")]
    pub nominal_result: Option<&'a crate::nominal::NominalAnalysis>,
    /// Alternating automaton analysis.
    #[cfg(feature = "alternating")]
    pub alternating_result: Option<&'a crate::alternating::AlternatingAnalysis>,
    /// LTL model checking results.
    #[cfg(feature = "ltl")]
    pub ltl_results: Option<&'a Vec<crate::ltl::LtlCheckResult>>,
    /// Provenance tracking results.
    #[cfg(feature = "provenance")]
    pub provenance_result: Option<&'a crate::provenance::ProvenanceAnalysis>,
    /// Cost register automaton analysis.
    #[cfg(feature = "cra")]
    pub cra_result: Option<&'a crate::cra::CraAnalysis>,
    /// Theory morphism check.
    #[cfg(feature = "morphisms")]
    pub morphism_result: Option<&'a crate::morphism::MorphismCheck>,
    /// KAT check (Hoare triples, equivalences).
    #[cfg(feature = "kat")]
    pub kat_result: Option<&'a crate::kat::KatCheck>,
}

/// Run all lints and return structured diagnostics.
///
/// Lints are grouped by category and run in order:
/// 1. Grammar structure (G01-G10)
/// 2. WFST-specific (W01-W06)
/// 3. Recovery (R01-R07)
/// 4. Cross-category (C01-C04)
/// 5. Performance (P02-P04)
pub fn run_lints(ctx: &LintContext) -> Vec<LintDiagnostic> {
    let mut diagnostics = Vec::new();

    // ── Grammar structure lints ──
    lint_g01_left_recursion(ctx, &mut diagnostics);
    lint_g02_unused_category(ctx, &mut diagnostics);
    lint_g03_ambiguous_prefix(ctx, &mut diagnostics);
    lint_g04_duplicate_rule_label(ctx, &mut diagnostics);
    lint_g05_empty_category(ctx, &mut diagnostics);
    lint_g06_shadowed_operator(ctx, &mut diagnostics);
    lint_g07_identical_rules(ctx, &mut diagnostics);
    lint_g24_alpha_equivalent_rules(ctx, &mut diagnostics);
    lint_g08_missing_cast_to_root(ctx, &mut diagnostics);
    lint_g09_unbalanced_delimiters(ctx, &mut diagnostics);
    lint_g10_ambiguous_associativity(ctx, &mut diagnostics);

    // ── WFST lints ──
    lint_w01_dead_rule(ctx, &mut diagnostics);
    lint_w02_nfa_ambiguous_prefix(ctx, &mut diagnostics);
    lint_w03_high_ambiguity_token(ctx, &mut diagnostics);
    lint_w04_weight_gap_anomaly(ctx, &mut diagnostics);
    // W05: Insert pre-collected composed-dispatch-ambiguity diagnostics
    diagnostics.extend(ctx.pre_collected_diagnostics.iter().cloned());
    lint_w06_weight_inversion(ctx, &mut diagnostics);
    lint_w10_spillover_eliminable_by_lookahead(ctx, &mut diagnostics);
    lint_w11_context_narrowing_deterministic(ctx, &mut diagnostics);
    #[cfg(feature = "wfst-log")]
    lint_w12_training_would_improve(ctx, &mut diagnostics);

    // ── Recovery lints ──
    lint_r01_empty_sync_set(ctx, &mut diagnostics);
    lint_r02_sparse_recovery(ctx, &mut diagnostics);
    lint_r05_missing_bracket_sync(ctx, &mut diagnostics);
    lint_r06_inverted_recovery_costs(ctx, &mut diagnostics);
    lint_r07_transposition_candidate(ctx, &mut diagnostics);

    // ── Cross-category lints ──
    lint_c01_cast_cycle(ctx, &mut diagnostics);
    lint_c02_transitive_cast_redundancy(ctx, &mut diagnostics);
    lint_c04_wide_cross_overlap(ctx, &mut diagnostics);

    // ── Performance lints ──
    lint_p02_high_nfa_spillover(ctx, &mut diagnostics);
    lint_p03_deep_cast_nesting(ctx, &mut diagnostics);
    lint_p04_many_alternatives(ctx, &mut diagnostics);

    // ── WPDS-derived lints ──
    lint_w13_wpds_unreachable(ctx, &mut diagnostics);
    lint_w14_wpds_confirmed_ambiguity(ctx, &mut diagnostics);
    lint_w16_wpds_weight_inversion(ctx, &mut diagnostics);
    lint_d14_wpds_complexity_report(ctx, &mut diagnostics);
    lint_p05_wpds_pipeline_cost(ctx, &mut diagnostics);
    lint_comp08_refactoring_suggestions(ctx, &mut diagnostics);

    // ── PathMap-derived lints ──
    lint_w03_cross_category_hotspot(ctx, &mut diagnostics);
    lint_g32_prefix_isomorphism(ctx, &mut diagnostics);
    lint_d10_lookahead_waste(ctx, &mut diagnostics);
    lint_d13_ascent_trie_correlation(ctx, &mut diagnostics);

    // ── Mathematical analysis lints ──

    // TRS analysis (confluence + termination)
    #[cfg(feature = "trs-analysis")]
    {
        lint_t01_non_joinable_critical_pair(ctx, &mut diagnostics);
        lint_t02_confluence_verified(ctx, &mut diagnostics);
        lint_t03_non_terminating_cycle(ctx, &mut diagnostics);
        lint_t04_termination_verified(ctx, &mut diagnostics);
    }

    // VPA analysis
    #[cfg(feature = "vpa")]
    {
        lint_v01_vpa_determinizable(ctx, &mut diagnostics);
        lint_v02_vpa_alphabet_mismatch(ctx, &mut diagnostics);
    }

    // WTA analysis
    #[cfg(feature = "tree-automata")]
    {
        lint_v03_wta_unrecognized_term(ctx, &mut diagnostics);
        lint_v04_wta_hot_path(ctx, &mut diagnostics);
    }

    // Safety verification
    lint_s01_safety_violation(ctx, &mut diagnostics);
    lint_s02_safety_verified(ctx, &mut diagnostics);

    // CEGAR
    lint_s03_cegar_refinement(ctx, &mut diagnostics);

    // EWPDS
    #[cfg(feature = "wpds-extended")]
    lint_s04_ewpds_merge_site(ctx, &mut diagnostics);

    // ARA
    #[cfg(feature = "wpds-ara")]
    lint_s05_ara_invariant(ctx, &mut diagnostics);

    // Algebraic
    lint_s06_algebraic_summary(ctx, &mut diagnostics);

    // Petri nets
    #[cfg(feature = "petri")]
    {
        lint_n01_deadlock_risk(ctx, &mut diagnostics);
        lint_n02_unbounded_channel(ctx, &mut diagnostics);
    }

    // Nominal automata
    #[cfg(feature = "nominal")]
    {
        lint_n03_scope_violation(ctx, &mut diagnostics);
        lint_n04_scope_narrowing(ctx, &mut diagnostics);
    }

    // Alternating automata
    #[cfg(feature = "alternating")]
    lint_n05_non_bisimilar(ctx, &mut diagnostics);

    // LTL model checking
    #[cfg(feature = "ltl")]
    {
        lint_l01_ltl_violated(ctx, &mut diagnostics);
        lint_l02_ltl_verified(ctx, &mut diagnostics);
    }

    // Provenance
    #[cfg(feature = "provenance")]
    lint_e01_provenance_trace(ctx, &mut diagnostics);

    // CRA
    #[cfg(feature = "cra")]
    lint_e02_cra_cost_anomaly(ctx, &mut diagnostics);

    // Morphisms
    #[cfg(feature = "morphisms")]
    {
        lint_m01_morphism_gap(ctx, &mut diagnostics);
        lint_m02_morphism_preservation_failure(ctx, &mut diagnostics);
    }

    // KAT
    #[cfg(feature = "kat")]
    {
        lint_k01_hoare_failure(ctx, &mut diagnostics);
        lint_k02_kat_equivalence(ctx, &mut diagnostics);
    }

    // P06: Analysis pipeline timing
    lint_p06_analysis_pipeline_cost(ctx, &mut diagnostics);

    diagnostics
}

/// Emit all lint diagnostics to stderr (plain text).
pub fn emit_diagnostics(diagnostics: &[LintDiagnostic]) {
    for diag in diagnostics {
        eprintln!("{}", diag);
    }
}

/// Emit a single diagnostic to stderr with ANSI-colorized output.
pub fn emit_diagnostic(diag: &LintDiagnostic) {
    eprintln!("{}", format_diagnostic_colored(diag));
}

// ══════════════════════════════════════════════════════════════════════════════
// ANSI color constants (no external dependency — matches pipeline.rs style)
// ══════════════════════════════════════════════════════════════════════════════

#[allow(dead_code)]
pub mod ansi {
    pub const RESET: &str = "\x1b[0m";
    pub const BOLD: &str = "\x1b[1m";
    pub const DIM: &str = "\x1b[2m";
    pub const RED: &str = "\x1b[31m";
    pub const GREEN: &str = "\x1b[32m";
    pub const YELLOW: &str = "\x1b[33m";
    pub const BLUE: &str = "\x1b[34m";
    pub const CYAN: &str = "\x1b[36m";
    pub const BOLD_RED: &str = "\x1b[1;31m";
    pub const BOLD_YELLOW: &str = "\x1b[1;33m";
    pub const BOLD_CYAN: &str = "\x1b[1;36m";
    pub const BOLD_BLUE: &str = "\x1b[1;34m";
}

/// Format a single lint diagnostic with ANSI colors.
///
/// Color scheme:
/// - Error: bold red label + ID
/// - Warning: bold yellow label + ID
/// - Note / Info: bold cyan label + ID
/// - Grammar name: dim parentheses after `[ID]` when present
/// - Source location (`-->`): bold blue
/// - Category/rule context (`= in`): dim
/// - Hint (`= hint:`): green
/// - Backtick-quoted identifiers: bold
pub fn format_diagnostic_colored(diag: &LintDiagnostic) -> String {
    use std::fmt::Write;
    let mut out = String::with_capacity(256);

    // Severity label + lint ID
    let (label_color, id_color) = match diag.severity {
        LintSeverity::Error => (ansi::BOLD_RED, ansi::BOLD_RED),
        LintSeverity::Warning => (ansi::BOLD_YELLOW, ansi::BOLD_YELLOW),
        LintSeverity::Note | LintSeverity::Info => (ansi::BOLD_CYAN, ansi::BOLD_CYAN),
    };

    // Colorize backtick-quoted identifiers in the message
    let message = colorize_backtick_spans(&diag.message, ansi::BOLD, ansi::RESET);

    write!(
        out,
        "{}{}{}[{}{}{}]",
        label_color, diag.severity, ansi::RESET,
        id_color, diag.id, ansi::RESET,
    ).expect("write to String");

    // Grammar name in dim parentheses after [ID]
    if let Some(ref grammar) = diag.grammar_name {
        write!(out, " {}({}){}",  ansi::DIM, grammar, ansi::RESET).expect("write to String");
    }

    write!(out, ": {}", message).expect("write to String");

    // Source location (rustc-style `-->` pointer)
    if let Some(ref loc) = diag.source_location {
        if loc.line > 0 {
            write!(
                out,
                "\n  {}{}{} <macro>:{}",
                ansi::BOLD_BLUE, "-->", ansi::RESET, loc,
            ).expect("write to String");
        }
    }

    // Category/rule context
    match (&diag.category, &diag.rule) {
        (Some(cat), Some(rule)) => {
            write!(
                out,
                "\n  {}= in category `{}`, rule `{}`{}",
                ansi::DIM, cat, rule, ansi::RESET,
            ).expect("write to String");
        }
        (Some(cat), None) => {
            write!(
                out,
                "\n  {}= in category `{}`{}",
                ansi::DIM, cat, ansi::RESET,
            ).expect("write to String");
        }
        _ => {}
    }

    // Hint
    if let Some(ref hint) = diag.hint {
        let hint_colored = colorize_backtick_spans(hint, ansi::BOLD, ansi::GREEN);
        write!(
            out,
            "\n  {}= hint: {}{}",
            ansi::GREEN, hint_colored, ansi::RESET,
        ).expect("write to String");
    }

    out
}

/// Replace backtick-quoted spans `` `foo` `` with bold formatting.
///
/// Scans for matching pairs of backticks and wraps the enclosed text
/// (including backticks) with the given ANSI start/end codes.
pub fn colorize_backtick_spans(text: &str, start: &str, end: &str) -> String {
    let mut result = String::with_capacity(text.len() + 64);
    let mut chars = text.char_indices().peekable();

    while let Some((i, ch)) = chars.next() {
        if ch == '`' {
            // Find closing backtick
            if let Some(close_pos) = text[i + 1..].find('`') {
                let close = i + 1 + close_pos;
                result.push_str(start);
                result.push_str(&text[i..=close]);
                result.push_str(end);
                // Advance past the closing backtick
                while chars.peek().is_some_and(|&(j, _)| j <= close) {
                    chars.next();
                }
            } else {
                result.push(ch);
            }
        } else {
            result.push(ch);
        }
    }
    result
}

/// Emit all lint diagnostics to stderr with ANSI-colorized output and a grammar-name header.
///
/// When `PRATTAIL_LINT_VERBOSE` is set, emits individual diagnostics (useful for CI/filtering).
/// Otherwise, groups repeated lint IDs into compact summaries via [`group_diagnostics()`].
pub fn emit_diagnostics_for_grammar(grammar_name: &str, diagnostics: &[LintDiagnostic]) {
    if diagnostics.is_empty() {
        return;
    }
    eprintln!(
        "  {}linting{} grammar `{}`",
        ansi::BOLD_CYAN, ansi::RESET, grammar_name,
    );
    let verbose = std::env::var("PRATTAIL_LINT_VERBOSE").is_ok();
    if verbose {
        for diag in diagnostics {
            eprintln!("{}", format_diagnostic_colored(diag));
        }
    } else {
        let grouped = group_diagnostics(diagnostics.to_vec());
        for diag in &grouped {
            eprintln!("{}", format_diagnostic_colored(diag));
        }
    }
}

/// Returns true if any diagnostic has Error severity.
pub fn has_errors(diagnostics: &[LintDiagnostic]) -> bool {
    diagnostics.iter().any(|d| d.severity == LintSeverity::Error)
}

// ══════════════════════════════════════════════════════════════════════════════
// Diagnostic Grouping
// ══════════════════════════════════════════════════════════════════════════════

/// Known lint IDs eligible for grouping.
const GROUPABLE_IDS: &[&str] = &[
    "W01", "W02", "W03", "W05", "W07", "G03", "G08", "G27",
    "D01", "D02", "D03", "D08", "D09",
];

/// Group repeated lint diagnostics into compact summaries.
///
/// Partitions input by lint ID. Known groupable IDs delegate to per-ID
/// groupers; all other IDs pass through unchanged. Single-item groups
/// always pass through unchanged. Grouped results replace the **first
/// occurrence** position of each grouped ID, preserving relative ordering.
pub fn group_diagnostics(diagnostics: Vec<LintDiagnostic>) -> Vec<LintDiagnostic> {
    use std::collections::BTreeMap;

    if diagnostics.len() <= 1 {
        return diagnostics;
    }

    // Partition by lint ID, tracking first-occurrence index per ID
    let mut by_id: BTreeMap<&str, Vec<LintDiagnostic>> = BTreeMap::new();
    let mut first_index: HashMap<&str, usize> = HashMap::new();
    let mut non_groupable: Vec<(usize, LintDiagnostic)> = Vec::new();

    for (i, diag) in diagnostics.into_iter().enumerate() {
        if GROUPABLE_IDS.contains(&diag.id) {
            first_index.entry(diag.id).or_insert(i);
            by_id.entry(diag.id).or_default().push(diag);
        } else {
            non_groupable.push((i, diag));
        }
    }

    // Build grouped results with their first-occurrence index
    let mut indexed: Vec<(usize, Vec<LintDiagnostic>)> = Vec::new();

    for (id, items) in by_id {
        let idx = first_index[id];
        if items.len() == 1 {
            indexed.push((idx, items));
        } else {
            let grouped = match id {
                "W01" => group_w01(items),
                "W02" => group_w02(items),
                "W03" => group_w03(items),
                "W05" => group_w05(items),
                "W07" => group_w07(items),
                "G03" => group_g03(items),
                "G08" => group_g08(items),
                "G27" => group_g27(items),
                "D01" => group_ambiguity_by_category("D01", "precision-ambiguity", "precision ambiguity", items),
                "D02" => group_ambiguity_by_category("D02", "unresolvable-ambiguity", "unresolvable ambiguity", items),
                "D03" => group_ambiguity_by_category("D03", "trie-unreachable-rule", "unreachable trie rule(s)", items),
                "D08" => group_ambiguity_by_category("D08", "optimization-suggestion", "optimization suggestion(s)", items),
                "D09" => group_ambiguity_by_category("D09", "conflict-resolution-guide", "conflict resolution guidance", items),
                _ => items, // unreachable due to GROUPABLE_IDS check
            };
            indexed.push((idx, grouped));
        }
    }

    // Merge non-groupable items
    for (i, diag) in non_groupable {
        indexed.push((i, vec![diag]));
    }

    // Sort by first-occurrence index to preserve relative ordering
    indexed.sort_by_key(|(i, _)| *i);
    indexed.into_iter().flat_map(|(_, diags)| diags).collect()
}

/// Group W01 (dead-rule) diagnostics by hint text (= warning type), then by category.
///
/// Output: `"N rules are unreachable...\n  Cat1: R1, R2\n  Cat2: R3"`
fn group_w01(diagnostics: Vec<LintDiagnostic>) -> Vec<LintDiagnostic> {
    use std::collections::BTreeMap;

    // Group by hint text (each hint corresponds to a different dead-rule tier)
    let mut by_hint: BTreeMap<String, Vec<LintDiagnostic>> = BTreeMap::new();
    for diag in diagnostics {
        let key = diag.hint.clone().unwrap_or_default();
        by_hint.entry(key).or_default().push(diag);
    }

    let mut result = Vec::new();
    for (hint_key, items) in by_hint {
        if items.len() == 1 {
            result.extend(items);
            continue;
        }

        // Sub-group by category
        let mut by_cat: BTreeMap<String, Vec<String>> = BTreeMap::new();
        for diag in &items {
            let cat = diag.category.clone().unwrap_or_else(|| "unknown".to_string());
            let rule = diag.rule.clone().unwrap_or_else(|| "?".to_string());
            by_cat.entry(cat).or_default().push(rule);
        }

        let total = items.len();
        let cat_lines: Vec<String> = by_cat
            .iter()
            .map(|(cat, rules)| format!("  {}: {}", cat, rules.join(", ")))
            .collect();

        let first = &items[0];
        result.push(LintDiagnostic {
            id: first.id,
            name: first.name,
            severity: first.severity,
            category: None,
            rule: None,
            message: format!(
                "{} rules are unreachable (dead code)\n{}",
                total,
                cat_lines.join("\n"),
            ),
            hint: Some(hint_key),
            grammar_name: first.grammar_name.clone(),
            source_location: None,
        });
    }
    result
}

/// Group W02 (nfa-ambiguous-prefix) by category.
///
/// Output: `"ambiguous prefix dispatch in N categories\n  Cat: token matches [R1, R2]; ..."`
fn group_w02(diagnostics: Vec<LintDiagnostic>) -> Vec<LintDiagnostic> {
    group_ambiguity_by_category("W02", "nfa-ambiguous-prefix", "ambiguous NFA prefix dispatch", diagnostics)
}

/// Group W03 (high-ambiguity-token) by category.
fn group_w03(diagnostics: Vec<LintDiagnostic>) -> Vec<LintDiagnostic> {
    group_ambiguity_by_category("W03", "high-ambiguity-token", "high-ambiguity tokens", diagnostics)
}

/// Group W05 (composed-dispatch-ambiguity) by category.
///
/// Output: `"N ambiguities resolved by tropical shortest path\n  Cat: details..."`
fn group_w05(diagnostics: Vec<LintDiagnostic>) -> Vec<LintDiagnostic> {
    use std::collections::BTreeMap;

    let mut by_cat: BTreeMap<String, Vec<LintDiagnostic>> = BTreeMap::new();
    for diag in diagnostics {
        let cat = diag.category.clone().unwrap_or_else(|| "unknown".to_string());
        by_cat.entry(cat).or_default().push(diag);
    }

    // If only one category with one item, pass through
    if by_cat.len() == 1 && by_cat.values().next().map_or(false, |v| v.len() == 1) {
        return by_cat.into_values().flatten().collect();
    }

    let total: usize = by_cat.values().map(|v| v.len()).sum();
    let first = by_cat.values().next().and_then(|v| v.first());
    let (grammar_name, hint) = match first {
        Some(d) => (d.grammar_name.clone(), d.hint.clone()),
        None => return Vec::new(),
    };

    // Build per-category summary lines
    let mut cat_lines: Vec<String> = Vec::new();
    for (cat, items) in &by_cat {
        let summaries: Vec<String> = items
            .iter()
            .filter_map(|d| {
                // Extract winner from message: "Resolved by tropical shortest path → WINNER"
                let msg = &d.message;
                let winner = msg.rsplit("→ ").next().unwrap_or("?").trim();
                // Extract token entries: lines starting with "  - Token::"
                let entries: Vec<&str> = msg
                    .lines()
                    .filter(|l| l.trim_start().starts_with("- Token::"))
                    .collect();
                if entries.is_empty() {
                    return None;
                }
                // Summarize: "Token1→Rule1, Token2→Rule2 (vs Loser, wt X.XX)"
                let mut parts = Vec::new();
                let mut losers = Vec::new();
                for entry in &entries {
                    // Format: "  - Token::Variant → rule Label (weight X.XX)"
                    let trimmed = entry.trim_start().trim_start_matches("- Token::");
                    if let Some((variant_rule, weight_part)) = trimmed.split_once(" (weight ") {
                        let weight = weight_part.trim_end_matches(')');
                        if let Some((variant, rule)) = variant_rule.split_once(" → rule ") {
                            if rule.trim() == winner {
                                parts.push(format!("{}→{}", variant.trim(), rule.trim()));
                            } else {
                                losers.push(format!("{} wt {}", rule.trim(), weight));
                            }
                        }
                    }
                }
                let vs_str = if losers.is_empty() {
                    String::new()
                } else {
                    format!(" (vs {})", losers.join(", "))
                };
                if parts.is_empty() {
                    Some(format!("→ {}{}", winner, vs_str))
                } else {
                    Some(format!("{}{}", parts.join(", "), vs_str))
                }
            })
            .collect();
        cat_lines.push(format!("  {}: {}", cat, summaries.join("; ")));
    }

    vec![LintDiagnostic {
        id: "W05",
        name: "composed-dispatch-ambiguity",
        severity: LintSeverity::Warning,
        category: None,
        rule: None,
        message: format!(
            "{} ambiguities resolved by tropical shortest path\n{}",
            total,
            cat_lines.join("\n"),
        ),
        hint,
        grammar_name,
        source_location: None,
    }]
}

/// Group W07 (nearly-dead-path) by category.
///
/// Output: `"N rules on nearly-dead paths\n  Cat: R1, R2"`
fn group_w07(diagnostics: Vec<LintDiagnostic>) -> Vec<LintDiagnostic> {
    use std::collections::BTreeMap;

    let mut by_cat: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for diag in &diagnostics {
        let cat = diag.category.clone().unwrap_or_else(|| "unknown".to_string());
        let rule = diag.rule.clone().unwrap_or_else(|| "?".to_string());
        by_cat.entry(cat).or_default().push(rule);
    }

    let total = diagnostics.len();
    let first = &diagnostics[0];

    let cat_lines: Vec<String> = by_cat
        .iter()
        .map(|(cat, rules)| format!("  {}: {}", cat, rules.join(", ")))
        .collect();

    vec![LintDiagnostic {
        id: first.id,
        name: first.name,
        severity: first.severity,
        category: None,
        rule: None,
        message: format!(
            "{} rules on nearly-dead paths\n{}",
            total,
            cat_lines.join("\n"),
        ),
        hint: first.hint.clone(),
        grammar_name: first.grammar_name.clone(),
        source_location: None,
    }]
}

/// Group G03 (ambiguous-prefix) by category.
///
/// Output: `"ambiguous prefix dispatch in N categories\n  Cat: token1 matches [R1, R2]; ..."`
fn group_g03(diagnostics: Vec<LintDiagnostic>) -> Vec<LintDiagnostic> {
    group_ambiguity_by_category("G03", "ambiguous-prefix", "ambiguous prefix dispatch", diagnostics)
}

/// Group G08 (missing-cast-to-root) into a single diagnostic listing all isolated categories.
///
/// Output: `"N categories have no cast path to primary\n  isolated: Cat1, Cat2, Cat3"`
fn group_g08(diagnostics: Vec<LintDiagnostic>) -> Vec<LintDiagnostic> {
    let cats: Vec<String> = diagnostics
        .iter()
        .filter_map(|d| d.category.clone())
        .collect();

    let first = &diagnostics[0];

    // Extract primary category from the first diagnostic's message
    let primary = first
        .message
        .rsplit("to primary category `")
        .next()
        .and_then(|s| s.strip_suffix('`'))
        .unwrap_or("?");

    vec![LintDiagnostic {
        id: first.id,
        name: first.name,
        severity: first.severity,
        category: None,
        rule: None,
        message: format!(
            "{} categories have no cast path to primary category `{}`\n  isolated: {}",
            cats.len(),
            primary,
            cats.join(", "),
        ),
        hint: Some(format!(
            "add cast rules from these categories to `{}` or an intermediate category",
            primary,
        )),
        grammar_name: first.grammar_name.clone(),
        source_location: None,
    }]
}

/// Group G27 (rule-subsumption-candidate) by general rule name (from the `rule` field).
///
/// Output: `"N rules may be subsumed by more general rule `General`\n  candidates: R1, R2"`
fn group_g27(diagnostics: Vec<LintDiagnostic>) -> Vec<LintDiagnostic> {
    use std::collections::BTreeMap;

    // Group by general rule name (extracted from message)
    let mut by_general: BTreeMap<String, Vec<LintDiagnostic>> = BTreeMap::new();
    for diag in diagnostics {
        // Extract general rule name: "... subsumed by more general rule `GENERAL` ..."
        let general = diag
            .message
            .split("more general rule `")
            .nth(1)
            .and_then(|s| s.split('`').next())
            .unwrap_or("?")
            .to_string();
        by_general.entry(general).or_default().push(diag);
    }

    let mut result = Vec::new();
    for (general_name, items) in by_general {
        if items.len() == 1 {
            result.extend(items);
            continue;
        }

        // Collect specific rule names from messages
        let specific_names: Vec<String> = items
            .iter()
            .filter_map(|d| {
                // "rule `SPECIFIC` may be subsumed..."
                d.message
                    .split("rule `")
                    .nth(1)
                    .and_then(|s| s.split('`').next())
                    .map(|s| s.to_string())
            })
            .collect();

        let first = &items[0];
        result.push(LintDiagnostic {
            id: first.id,
            name: first.name,
            severity: first.severity,
            category: None,
            rule: None,
            message: format!(
                "{} rules may be subsumed by more general rule `{}`\n  candidates: {}",
                items.len(),
                general_name,
                specific_names.join(", "),
            ),
            hint: Some(format!(
                "review whether these rules can be removed or merged with `{}`",
                general_name,
            )),
            grammar_name: first.grammar_name.clone(),
            source_location: None,
        });
    }
    result
}

/// Shared helper for grouping ambiguity-style diagnostics (W02, W03, G03) by category.
///
/// Each diagnostic's message is preserved as a sub-item under its category.
fn group_ambiguity_by_category(
    id: &'static str,
    name: &'static str,
    description: &str,
    diagnostics: Vec<LintDiagnostic>,
) -> Vec<LintDiagnostic> {
    use std::collections::BTreeMap;

    let mut by_cat: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for diag in &diagnostics {
        let cat = diag.category.clone().unwrap_or_else(|| "unknown".to_string());
        by_cat.entry(cat).or_default().push(diag.message.clone());
    }

    let total = diagnostics.len();
    let first = &diagnostics[0];

    let cat_lines: Vec<String> = by_cat
        .iter()
        .map(|(cat, msgs)| {
            if msgs.len() == 1 {
                format!("  {}: {}", cat, msgs[0])
            } else {
                let items: Vec<String> = msgs.iter().enumerate().map(|(i, m)| {
                    format!("  {}[{}]: {}", cat, i + 1, m)
                }).collect();
                items.join("\n")
            }
        })
        .collect();

    vec![LintDiagnostic {
        id,
        name,
        severity: first.severity,
        category: None,
        rule: None,
        message: format!(
            "{} {} in {} categories\n{}",
            total,
            description,
            by_cat.len(),
            cat_lines.join("\n"),
        ),
        hint: first.hint.clone(),
        grammar_name: first.grammar_name.clone(),
        source_location: None,
    }]
}

// ══════════════════════════════════════════════════════════════════════════════
// G01: Left Recursion (migrated from prediction.rs)
// ══════════════════════════════════════════════════════════════════════════════

fn lint_g01_left_recursion(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    for (label, category, syntax) in ctx.all_syntax {
        if let Some(SyntaxItemSpec::NonTerminal { category: ref first_cat, .. }) = syntax.first() {
            if first_cat == category {
                // Skip infix, postfix, mixfix — handled by Pratt
                let terminal_count = syntax
                    .iter()
                    .filter(|i| matches!(i, SyntaxItemSpec::Terminal(_)))
                    .count();
                let nt_count = syntax
                    .iter()
                    .filter(|i| matches!(i, SyntaxItemSpec::NonTerminal { .. }))
                    .count();

                let is_infix_pattern = nt_count == 2
                    && terminal_count >= 1
                    && syntax.len() >= 3
                    && matches!(
                        syntax.last(),
                        Some(SyntaxItemSpec::NonTerminal { category: ref last_cat, .. })
                        if last_cat == category
                    );
                let is_postfix_pattern =
                    nt_count == 1 && terminal_count == 1 && syntax.len() == 2;
                let is_mixfix_pattern = nt_count >= 3 && terminal_count >= 2;

                if !is_infix_pattern && !is_postfix_pattern && !is_mixfix_pattern {
                    diagnostics.push(LintDiagnostic {
                        id: "G01",
                        name: "left-recursion",
                        severity: LintSeverity::Warning,
                        category: Some(category.clone()),
                        rule: Some(label.clone()),
                        message: format!(
                            "left-recursive rule `{}` in category `{}` \
                             (first item is NonTerminal of same category)",
                            label, category,
                        ),
                        hint: Some(
                            "convert to infix/postfix pattern for Pratt handling, \
                             or restructure to avoid same-category leading NonTerminal"
                                .to_string(),
                        ),
                        grammar_name: Some(ctx.grammar_name.to_string()),
                        source_location: ctx.rule_locations.get(&(label.clone(), category.clone())).copied(),
                    });
                }
            }
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// G02: Unused Category (migrated from prediction.rs)
// ══════════════════════════════════════════════════════════════════════════════

fn lint_g02_unused_category(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let mut referenced: HashSet<String> = HashSet::new();

    for (_, _, syntax) in ctx.all_syntax {
        collect_referenced_categories(syntax, &mut referenced);
    }

    // Categories with rules targeting them are "used"
    for (_, category, _) in ctx.all_syntax {
        referenced.insert(category.clone());
    }

    let category_names: Vec<&str> = ctx.categories.iter().map(|c| c.name.as_str()).collect();
    for cat_name in &category_names {
        if !referenced.contains(*cat_name) {
            diagnostics.push(LintDiagnostic {
                id: "G02",
                name: "unused-category",
                severity: LintSeverity::Warning,
                category: Some(cat_name.to_string()),
                rule: None,
                message: format!(
                    "category `{}` declared but never referenced in any rule syntax",
                    cat_name,
                ),
                hint: Some("remove the unused category or add rules that reference it".to_string()),
                grammar_name: Some(ctx.grammar_name.to_string()),
                source_location: None,
            });
        }
    }
}

/// Recursively collect all category names referenced in syntax items.
fn collect_referenced_categories(items: &[SyntaxItemSpec], referenced: &mut HashSet<String>) {
    for item in items {
        match item {
            SyntaxItemSpec::NonTerminal { category, .. } => {
                referenced.insert(category.clone());
            }
            SyntaxItemSpec::Collection {
                element_category, ..
            } => {
                referenced.insert(element_category.clone());
            }
            SyntaxItemSpec::Sep { body, .. } => {
                collect_referenced_categories(std::slice::from_ref(body.as_ref()), referenced);
            }
            SyntaxItemSpec::Map { body_items } => {
                collect_referenced_categories(body_items, referenced);
            }
            SyntaxItemSpec::Zip {
                left_category,
                right_category,
                body,
                ..
            } => {
                referenced.insert(left_category.clone());
                referenced.insert(right_category.clone());
                collect_referenced_categories(std::slice::from_ref(body.as_ref()), referenced);
            }
            SyntaxItemSpec::Optional { inner } => {
                collect_referenced_categories(inner, referenced);
            }
            SyntaxItemSpec::Binder { category, .. } => {
                referenced.insert(category.clone());
            }
            _ => {}
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// G03: Ambiguous Prefix (migrated from prediction.rs)
// ══════════════════════════════════════════════════════════════════════════════

fn lint_g03_ambiguous_prefix(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    use crate::prediction::FirstItem;

    let category_names: Vec<String> = ctx.categories.iter().map(|c| c.name.clone()).collect();

    for cat in &category_names {
        // Collect non-infix, non-var, non-literal rules for this category
        let prefix_rules: Vec<&RuleInfo> = ctx
            .rules
            .iter()
            .filter(|r| r.category == *cat && !r.is_infix && !r.is_var && !r.is_literal)
            .collect();

        let mut terminal_to_rules: HashMap<String, Vec<String>> = HashMap::new();

        for rule in &prefix_rules {
            for item in &rule.first_items {
                if let FirstItem::Terminal(t) = item {
                    terminal_to_rules
                        .entry(t.clone())
                        .or_default()
                        .push(rule.label.clone());
                }
            }
        }

        for (token, rule_labels) in &terminal_to_rules {
            if rule_labels.len() > 1 {
                // Classify root cause via decision tree if available
                let root_cause = classify_ambiguity_root_cause(ctx, cat, token);

                let message = if let Some(cause) = &root_cause {
                    format!(
                        "ambiguous prefix on `{}` in category `{}`: rules [{}] — {}",
                        token, cat, rule_labels.join(", "), cause,
                    )
                } else {
                    format!(
                        "ambiguous prefix dispatch for token `{}` in category `{}`: \
                         rules [{}] all match",
                        token, cat, rule_labels.join(", "),
                    )
                };

                diagnostics.push(LintDiagnostic {
                    id: "G03",
                    name: "ambiguous-prefix",
                    severity: LintSeverity::Warning,
                    category: Some(cat.clone()),
                    rule: None,
                    message,
                    hint: Some(
                        "add unique dispatch tokens or use WFST weights to disambiguate"
                            .to_string(),
                    ),
                    grammar_name: Some(ctx.grammar_name.to_string()),
                    source_location: None,
                });
            }
        }
    }
}

/// Classify the root cause of a G03 ambiguity using the decision tree.
///
/// Returns a human-readable classification:
/// - FIRST token clash (branch at byte 0)
/// - Shared terminal prefix diverging at suffix (branch at byte N>0)
/// - Nonterminal boundary
/// - Cross-category overlap (cast collision)
fn classify_ambiguity_root_cause(
    ctx: &LintContext,
    category: &str,
    token: &str,
) -> Option<String> {
    let tree = ctx.decision_trees.get(category)?;
    let strategy = tree.dispatch_strategy(token, ctx.token_id_map);

    match strategy {
        crate::decision_tree::DispatchStrategy::NfaTryAll {
            rule_labels,
            shared_prefix_len,
            shared_terminals,
            ..
        } => {
            if shared_prefix_len == 0 && shared_terminals.is_empty() {
                // Branch at byte 0 — FIRST token clash
                Some(format!(
                    "FIRST token clash: {} rules share dispatch token with no distinguishing prefix",
                    rule_labels.len()
                ))
            } else {
                // Check if any shared byte is an NT boundary marker
                let has_nt_boundary = shared_terminals.iter().any(|&b| b >= 0x82 && b < 0xC0);
                let has_optional = shared_terminals.iter().any(|&b| b == 0xC0 || b == 0xC1);

                if has_nt_boundary {
                    Some(format!(
                        "nonterminal boundary divergence after {}-token shared prefix",
                        shared_prefix_len
                    ))
                } else if has_optional {
                    Some(format!(
                        "optional group nesting divergence after {}-token shared prefix",
                        shared_prefix_len
                    ))
                } else {
                    // Shared terminal prefix diverging at suffix
                    let shared_names: Vec<String> = shared_terminals.iter()
                        .filter_map(|&b| {
                            ctx.token_id_map.name(b as u16).map(|n| format!("`{}`", n))
                        })
                        .collect();
                    if shared_names.is_empty() {
                        Some(format!(
                            "shared {}-token prefix diverges at suffix",
                            shared_prefix_len
                        ))
                    } else {
                        Some(format!(
                            "shared prefix [{}] ({} tokens) diverges at suffix",
                            shared_names.join(" "),
                            shared_prefix_len
                        ))
                    }
                }
            }
        }
        crate::decision_tree::DispatchStrategy::DisjointSuffix { .. } => {
            // Disjoint suffix = resolved, not actually ambiguous at runtime
            Some("resolved by disjoint suffix dispatch (no runtime ambiguity)".to_string())
        }
        _ => None,
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// G04: Duplicate Rule Label
// ══════════════════════════════════════════════════════════════════════════════

fn lint_g04_duplicate_rule_label(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let mut seen: HashMap<(&str, &str), &str> = HashMap::new();
    for (label, category, _) in ctx.all_syntax {
        let key = (category.as_str(), label.as_str());
        if let Some(&_existing) = seen.get(&key) {
            diagnostics.push(LintDiagnostic {
                id: "G04",
                name: "duplicate-rule-label",
                severity: LintSeverity::Error,
                category: Some(category.clone()),
                rule: Some(label.clone()),
                message: format!(
                    "duplicate rule label `{}` in category `{}` — codegen will produce \
                     conflicting constructor names",
                    label, category,
                ),
                hint: Some("rename one of the rules to a unique label".to_string()),
                grammar_name: Some(ctx.grammar_name.to_string()),
                source_location: ctx.rule_locations.get(&(label.clone(), category.clone())).copied(),
            });
        } else {
            seen.insert(key, label.as_str());
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// G05: Empty Category
// ══════════════════════════════════════════════════════════════════════════════

fn lint_g05_empty_category(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    for cat in ctx.categories.iter() {
        // Native-type categories (e.g., ![i64] as Int) are parsed via auto-generated
        // Pratt prefix match arms — they don't need explicit grammar rules.
        if cat.native_type.is_some() {
            continue;
        }
        let has_rules = ctx
            .all_syntax
            .iter()
            .any(|(_, category, _)| category.as_str() == cat.name);
        if !has_rules {
            diagnostics.push(LintDiagnostic {
                id: "G05",
                name: "empty-category",
                severity: LintSeverity::Warning,
                category: Some(cat.name.clone()),
                rule: None,
                message: format!(
                    "category `{}` has zero rules — cannot be parsed",
                    cat.name,
                ),
                hint: Some("add at least one rule or remove the category declaration".to_string()),
                grammar_name: Some(ctx.grammar_name.to_string()),
                source_location: None,
            });
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// G06: Shadowed Operator
// ══════════════════════════════════════════════════════════════════════════════

fn lint_g06_shadowed_operator(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    use crate::prediction::FirstItem;

    let category_names: Vec<String> = ctx.categories.iter().map(|c| c.name.clone()).collect();

    for cat in &category_names {
        // Collect terminals from infix rules
        let infix_terminals: HashSet<String> = ctx
            .bp_table
            .operators_for_category(cat)
            .iter()
            .map(|op| op.terminal.clone())
            .collect();

        // Collect terminals from prefix rules (non-infix, non-var, non-literal)
        let mut prefix_terminals: HashSet<String> = HashSet::new();
        for rule in ctx.rules.iter().filter(|r| {
            r.category == *cat && !r.is_infix && !r.is_var && !r.is_literal
        }) {
            for item in &rule.first_items {
                if let FirstItem::Terminal(t) = item {
                    prefix_terminals.insert(t.clone());
                }
            }
        }

        // Check for unary prefix rules specifically
        let unary_prefix_terminals: HashSet<String> = ctx
            .rules
            .iter()
            .filter(|r| r.category == *cat && !r.is_infix && !r.is_var && !r.is_literal)
            .flat_map(|r| {
                r.first_items.iter().filter_map(|fi| match fi {
                    FirstItem::Terminal(t) => Some(t.clone()),
                    _ => None,
                })
            })
            .collect();

        let overlap: Vec<&String> = infix_terminals
            .intersection(&unary_prefix_terminals)
            .collect();

        for terminal in overlap {
            diagnostics.push(LintDiagnostic {
                id: "G06",
                name: "shadowed-operator",
                severity: LintSeverity::Note,
                category: Some(cat.clone()),
                rule: None,
                message: format!(
                    "operator `{}` is both infix and prefix in category `{}`",
                    terminal, cat,
                ),
                hint: Some(
                    "this is intentional — prefix_bp = max_infix_bp + 2, so `-5!` = `-(5!)`"
                        .to_string(),
                ),
                grammar_name: Some(ctx.grammar_name.to_string()),
                source_location: None,
            });
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// G07: Identical Rules
// ══════════════════════════════════════════════════════════════════════════════

/// Normalize a syntax item sequence to a comparable string for G07.
fn syntax_signature(syntax: &[SyntaxItemSpec]) -> String {
    let mut parts = Vec::with_capacity(syntax.len());
    for item in syntax {
        match item {
            SyntaxItemSpec::Terminal(t) => parts.push(format!("T({})", t)),
            SyntaxItemSpec::NonTerminal { category, .. } => {
                parts.push(format!("NT({})", category))
            }
            SyntaxItemSpec::IdentCapture { .. } => parts.push("IDENT".to_string()),
            SyntaxItemSpec::Binder { category, is_multi, .. } => {
                parts.push(format!("BIND({},{})", category, is_multi))
            }
            SyntaxItemSpec::Collection {
                element_category,
                separator,
                kind,
                ..
            } => parts.push(format!("COL({},{},{:?})", element_category, separator, kind)),
            SyntaxItemSpec::Sep { body, separator, .. } => {
                let body_sig = syntax_signature(std::slice::from_ref(body.as_ref()));
                parts.push(format!("SEP({},{})", body_sig, separator))
            }
            SyntaxItemSpec::Map { body_items } => {
                let inner = syntax_signature(body_items);
                parts.push(format!("MAP({})", inner))
            }
            SyntaxItemSpec::Zip {
                left_category,
                right_category,
                body,
                ..
            } => {
                let body_sig = syntax_signature(std::slice::from_ref(body.as_ref()));
                parts.push(format!(
                    "ZIP({},{},{})",
                    left_category, right_category, body_sig
                ))
            }
            SyntaxItemSpec::BinderCollection { separator, .. } => {
                parts.push(format!("BCOL({})", separator))
            }
            SyntaxItemSpec::Optional { inner } => {
                let inner_sig = syntax_signature(inner);
                parts.push(format!("OPT({})", inner_sig))
            }
        }
    }
    parts.join("|")
}

fn lint_g07_identical_rules(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let category_names: Vec<String> = ctx.categories.iter().map(|c| c.name.clone()).collect();

    for cat in &category_names {
        let cat_syntax: Vec<(&str, &[SyntaxItemSpec])> = ctx
            .all_syntax
            .iter()
            .filter(|(_, c, _)| c == cat)
            .map(|(label, _, syntax)| (label.as_str(), syntax.as_slice()))
            .collect();

        let mut sig_to_labels: HashMap<String, Vec<&str>> = HashMap::new();
        for (label, syntax) in &cat_syntax {
            let sig = syntax_signature(syntax);
            sig_to_labels.entry(sig).or_default().push(label);
        }

        for (_, labels) in &sig_to_labels {
            if labels.len() > 1 {
                diagnostics.push(LintDiagnostic {
                    id: "G07",
                    name: "identical-rules",
                    severity: LintSeverity::Warning,
                    category: Some(cat.clone()),
                    rule: None,
                    message: format!(
                        "rules [{}] in category `{}` have identical syntax item sequences",
                        labels.join(", "),
                        cat,
                    ),
                    hint: Some(
                        "these rules are structurally identical — consider merging or \
                         differentiating their syntax"
                            .to_string(),
                    ),
                    grammar_name: Some(ctx.grammar_name.to_string()),
                    source_location: None,
                });
            }
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// G24: Alpha-Equivalent Rules (Sprint C: C1)
// ══════════════════════════════════════════════════════════════════════════════

/// De Bruijn encoding environment for canonical variable renaming.
///
/// Variables are assigned sequential slots in encounter order. The first
/// occurrence of a variable gets tag `0xC0` (NewVar), subsequent occurrences
/// get tag `0x80 | slot` (VarRef). Two rules with different variable names
/// but identical structure produce identical byte sequences.
struct DebruijnEnv {
    var_slots: HashMap<String, u8>,
    next_slot: u8,
}

impl DebruijnEnv {
    fn new() -> Self {
        Self {
            var_slots: HashMap::new(),
            next_slot: 0,
        }
    }

    /// Resolve a variable name to its De Bruijn encoding byte.
    ///
    /// - First occurrence: emits `0xC0` (NewVar) and assigns a slot
    /// - Subsequent occurrences: emits `0x80 | slot` (VarRef)
    fn resolve(&mut self, name: &str) -> u8 {
        if let Some(&slot) = self.var_slots.get(name) {
            // VarRef: seen before at this slot
            0x80 | slot
        } else {
            // NewVar: first encounter — assign next sequential slot.
            // The slot index is implicit from encounter order, making
            // the encoding independent of the concrete variable name.
            let slot = self.next_slot;
            self.next_slot = self.next_slot.saturating_add(1);
            self.var_slots.insert(name.to_string(), slot);
            0xC0
        }
    }
}

/// Encode a `SyntaxItemSpec` sequence to De Bruijn canonical bytes.
///
/// Two syntax sequences that differ only in variable naming (α-equivalent)
/// produce identical byte sequences. Terminals and category names are
/// encoded literally; variable references use De Bruijn encounter-order slots.
///
/// Tag layout (compatible with but independent of `pattern_codec.rs`):
/// - `0xC0` — NewVar (first occurrence of a variable)
/// - `0x80 | slot` — VarRef (subsequent reference to variable at slot)
/// - `0x01` — NonTerminal tag
/// - `0x02` — Binder tag
/// - `0x03` — Collection tag
/// - `0x04` — IdentCapture tag
/// - `0x05` — Sep tag
/// - `0x06` — Map tag
/// - `0x07` — Zip tag
/// - `0x08` — BinderCollection tag
/// - `0x09` — Optional tag
/// - `0x0A` — Terminal tag
/// - `0x0B` — End tag (closes Optional/Map/Sep)
fn syntax_item_debruijn_bytes(items: &[SyntaxItemSpec]) -> Vec<u8> {
    let mut env = DebruijnEnv::new();
    let mut buf = Vec::with_capacity(items.len() * 4);
    for item in items {
        encode_syntax_item(item, &mut env, &mut buf);
    }
    buf
}

/// Encode a single `SyntaxItemSpec` into the De Bruijn byte buffer.
fn encode_syntax_item(item: &SyntaxItemSpec, env: &mut DebruijnEnv, buf: &mut Vec<u8>) {
    match item {
        SyntaxItemSpec::Terminal(token) => {
            buf.push(0x0A); // Terminal tag
            let bytes = token.as_bytes();
            buf.push(bytes.len() as u8);
            buf.extend_from_slice(bytes);
        }
        SyntaxItemSpec::NonTerminal { category, param_name } => {
            // Variable reference for the param_name (De Bruijn encoded)
            buf.push(env.resolve(param_name));
            buf.push(0x01); // NonTerminal tag
            let cat_bytes = category.as_bytes();
            buf.push(cat_bytes.len() as u8);
            buf.extend_from_slice(cat_bytes);
        }
        SyntaxItemSpec::IdentCapture { param_name } => {
            buf.push(env.resolve(param_name));
            buf.push(0x04); // IdentCapture tag
        }
        SyntaxItemSpec::Binder { param_name, category, is_multi } => {
            buf.push(env.resolve(param_name));
            buf.push(0x02); // Binder tag
            buf.push(if *is_multi { 1 } else { 0 });
            let cat_bytes = category.as_bytes();
            buf.push(cat_bytes.len() as u8);
            buf.extend_from_slice(cat_bytes);
        }
        SyntaxItemSpec::Collection { param_name, element_category, separator, kind } => {
            buf.push(env.resolve(param_name));
            buf.push(0x03); // Collection tag
            let cat_bytes = element_category.as_bytes();
            buf.push(cat_bytes.len() as u8);
            buf.extend_from_slice(cat_bytes);
            let sep_bytes = separator.as_bytes();
            buf.push(sep_bytes.len() as u8);
            buf.extend_from_slice(sep_bytes);
            buf.push(*kind as u8);
        }
        SyntaxItemSpec::Sep { body, separator, kind } => {
            buf.push(0x05); // Sep tag
            let sep_bytes = separator.as_bytes();
            buf.push(sep_bytes.len() as u8);
            buf.extend_from_slice(sep_bytes);
            buf.push(*kind as u8);
            encode_syntax_item(body, env, buf);
            buf.push(0x0B); // End tag
        }
        SyntaxItemSpec::Map { body_items } => {
            buf.push(0x06); // Map tag
            for sub in body_items {
                encode_syntax_item(sub, env, buf);
            }
            buf.push(0x0B); // End tag
        }
        SyntaxItemSpec::Zip { left_name, right_name, left_category, right_category, body } => {
            buf.push(env.resolve(left_name));
            buf.push(env.resolve(right_name));
            buf.push(0x07); // Zip tag
            let lc = left_category.as_bytes();
            buf.push(lc.len() as u8);
            buf.extend_from_slice(lc);
            let rc = right_category.as_bytes();
            buf.push(rc.len() as u8);
            buf.extend_from_slice(rc);
            encode_syntax_item(body, env, buf);
            buf.push(0x0B); // End tag
        }
        SyntaxItemSpec::BinderCollection { param_name, separator } => {
            buf.push(env.resolve(param_name));
            buf.push(0x08); // BinderCollection tag
            let sep_bytes = separator.as_bytes();
            buf.push(sep_bytes.len() as u8);
            buf.extend_from_slice(sep_bytes);
        }
        SyntaxItemSpec::Optional { inner } => {
            buf.push(0x09); // Optional tag
            for sub in inner {
                encode_syntax_item(sub, env, buf);
            }
            buf.push(0x0B); // End tag
        }
    }
}

/// G24: Alpha-equivalent grammar rules.
///
/// Detects rules within the same category whose syntax item sequences are
/// identical up to variable renaming (α-equivalence). Uses De Bruijn
/// encounter-order encoding so that `rule A: x "+" y` and `rule B: a "+" b`
/// produce identical byte sequences, even though G07's string signatures differ.
///
/// Runs after G07 to avoid double-reporting: any pair already flagged by G07
/// (exact string match) is excluded from G24 results.
fn lint_g24_alpha_equivalent_rules(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let category_names: Vec<String> = ctx.categories.iter().map(|c| c.name.clone()).collect();

    for cat in &category_names {
        let cat_syntax: Vec<(&str, &[SyntaxItemSpec])> = ctx
            .all_syntax
            .iter()
            .filter(|(_, c, _)| c == cat)
            .map(|(label, _, syntax)| (label.as_str(), syntax.as_slice()))
            .collect();

        // Group by De Bruijn bytes
        let mut debruijn_groups: HashMap<Vec<u8>, Vec<&str>> = HashMap::new();
        for (label, syntax) in &cat_syntax {
            let bytes = syntax_item_debruijn_bytes(syntax);
            debruijn_groups.entry(bytes).or_default().push(label);
        }

        for (_, labels) in &debruijn_groups {
            if labels.len() < 2 {
                continue;
            }

            // Check if this group has identical string signatures — if so,
            // G07 already reports it. G24 only fires for groups where the
            // De Bruijn bytes match but the string signatures differ (true
            // α-equivalence that G07 misses: different variable names, same structure).
            let sigs: HashSet<String> = labels
                .iter()
                .map(|label| {
                    let syntax = cat_syntax
                        .iter()
                        .find(|(l, _)| l == label)
                        .map(|(_, s)| *s)
                        .expect("label must exist in cat_syntax");
                    syntax_signature(syntax)
                })
                .collect();
            if sigs.len() == 1 {
                // All have identical string signatures → G07 covers this
                continue;
            }

            diagnostics.push(LintDiagnostic {
                id: "G24",
                name: "alpha-equivalent-rules",
                severity: LintSeverity::Warning,
                category: Some(cat.clone()),
                rule: None,
                message: format!(
                    "rules [{}] in category `{}` are α-equivalent \
                     (identical up to variable renaming)",
                    labels.join(", "),
                    cat,
                ),
                hint: Some(
                    "these rules differ only in variable names — consider merging \
                     or differentiating their syntax structure"
                        .to_string(),
                ),
                grammar_name: Some(ctx.grammar_name.to_string()),
                source_location: None,
            });
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// G08: Missing Cast to Root
// ══════════════════════════════════════════════════════════════════════════════

/// G08: Checks **directed** cast/cross-cat graph reachability only (source→target
/// edges). A category that has no directed cast path *from itself to the primary*
/// is flagged. This is a grammar-structure lint focused on cast connectivity.
///
/// **Relationship with A4 (W01 InterCategoryDeadPath)**: A4 uses a richer
/// **undirected** graph that also includes syntax-level NonTerminal, Binder, and
/// Collection references. G08 can fire on categories that A4 does NOT flag (when
/// the category is syntax-connected but not cast-connected) and vice versa.
/// The two analyses are complementary, not redundant.
fn lint_g08_missing_cast_to_root(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    // Find primary (root) category
    let primary = match ctx.categories.iter().find(|c| c.is_primary) {
        Some(c) => &c.name,
        None => return,
    };

    // Build directed graph from cast rules: source → target
    let mut adjacency: HashMap<&str, HashSet<&str>> = HashMap::new();
    for cast in ctx.cast_rules {
        adjacency
            .entry(cast.source_category.as_str())
            .or_default()
            .insert(cast.target_category.as_str());
    }

    // Also add cross-category rules as edges
    for cross in ctx.cross_rules {
        adjacency
            .entry(cross.source_category.as_str())
            .or_default()
            .insert(cross.result_category.as_str());
    }

    // For each non-primary category, check if there's a path TO the primary category
    // (via cast/cross-category rules acting as edges in either direction)
    // A category needs a cast path FROM it TO the primary (the primary can parse it).
    // Actually: the question is whether the primary category can reach this category's values.
    // Cast rules go source → target (target wraps source). So target can receive source values.
    // We need: path from non-primary → primary via target edges.
    //
    // Build reverse graph: for each cast source→target, the target "imports" source values.
    // So primary can reach cat if: there's a path primary ←(imports)─ ... ←(imports)─ cat
    // Which means: path cat → ... → primary in the forward (source→target) graph.
    // Actually, cast rules mean target_category has a rule that wraps source_category.
    // So if we want cat's values to be usable in primary, we need a path from cat to primary
    // in the cast graph where each edge is source→target.

    let category_names: Vec<&str> = ctx.categories.iter().map(|c| c.name.as_str()).collect();

    for cat_name in &category_names {
        if *cat_name == primary.as_str() {
            continue;
        }

        // DFS from cat_name following source→target edges to see if we reach primary
        let mut visited = HashSet::new();
        let mut stack = vec![*cat_name];
        let mut found = false;

        while let Some(node) = stack.pop() {
            if node == primary.as_str() {
                found = true;
                break;
            }
            if !visited.insert(node) {
                continue;
            }
            if let Some(neighbors) = adjacency.get(node) {
                for &next in neighbors {
                    stack.push(next);
                }
            }
        }

        if !found {
            diagnostics.push(LintDiagnostic {
                id: "G08",
                name: "missing-cast-to-root",
                severity: LintSeverity::Warning,
                category: Some(cat_name.to_string()),
                rule: None,
                message: format!(
                    "no cast path from category `{}` to primary category `{}`",
                    cat_name, primary,
                ),
                hint: Some(format!(
                    "add a cast rule from `{}` to `{}` or an intermediate category",
                    cat_name, primary,
                )),
                grammar_name: Some(ctx.grammar_name.to_string()),
                source_location: None,
            });
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// G09: Unbalanced Delimiters
// ══════════════════════════════════════════════════════════════════════════════

fn lint_g09_unbalanced_delimiters(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let pairs = [('(', ')'), ('{', '}'), ('[', ']')];

    for (label, category, syntax) in ctx.all_syntax {
        let terminals = collect_terminals_flat(syntax);

        for &(open_char, close_char) in &pairs {
            // Count character occurrences across all terminals, not exact matches.
            // This correctly handles compound terminals like "in(" contributing 1
            // to the open-paren count, and self-balanced terminals like "()" contributing
            // 1 to each.
            let open_count: usize = terminals.iter()
                .map(|t| t.chars().filter(|&c| c == open_char).count())
                .sum();
            let close_count: usize = terminals.iter()
                .map(|t| t.chars().filter(|&c| c == close_char).count())
                .sum();

            if open_count != close_count {
                diagnostics.push(LintDiagnostic {
                    id: "G09",
                    name: "unbalanced-delimiters",
                    severity: LintSeverity::Warning,
                    category: Some(category.clone()),
                    rule: Some(label.clone()),
                    message: format!(
                        "rule `{}` in category `{}` has unbalanced delimiters: \
                         {} `{}` vs {} `{}`",
                        label, category, open_count, open_char, close_count, close_char,
                    ),
                    hint: Some(format!(
                        "add the missing `{}` delimiter",
                        if open_count > close_count { close_char } else { open_char },
                    )),
                    grammar_name: Some(ctx.grammar_name.to_string()),
                    source_location: ctx.rule_locations.get(&(label.clone(), category.clone())).copied(),
                });
            }
        }
    }
}

/// Collect all terminal strings from syntax items (flat, including nested).
fn collect_terminals_flat(items: &[SyntaxItemSpec]) -> Vec<String> {
    let mut terminals = Vec::new();
    for item in items {
        match item {
            SyntaxItemSpec::Terminal(t) => terminals.push(t.clone()),
            SyntaxItemSpec::Collection { separator, .. }
            | SyntaxItemSpec::BinderCollection { separator, .. } => {
                terminals.push(separator.clone());
            }
            SyntaxItemSpec::Sep { body, separator, .. } => {
                terminals.extend(collect_terminals_flat(std::slice::from_ref(body.as_ref())));
                terminals.push(separator.clone());
            }
            SyntaxItemSpec::Map { body_items } => {
                terminals.extend(collect_terminals_flat(body_items));
            }
            SyntaxItemSpec::Zip { body, .. } => {
                terminals.extend(collect_terminals_flat(std::slice::from_ref(body.as_ref())));
            }
            SyntaxItemSpec::Optional { inner } => {
                terminals.extend(collect_terminals_flat(inner));
            }
            _ => {}
        }
    }
    terminals
}

/// Get rule labels dispatched by a token in a category using the decision tree.
fn tree_rules_for_token(ctx: &LintContext, category: &str, token: &str) -> Vec<String> {
    let tree = match ctx.decision_trees.get(category) {
        Some(t) => t,
        None => return Vec::new(),
    };
    let variant = crate::automata::codegen::terminal_to_variant_name(token);
    let strategy = tree.dispatch_strategy(&variant, ctx.token_id_map);
    match strategy {
        crate::decision_tree::DispatchStrategy::Singleton { rule_label } => vec![rule_label],
        crate::decision_tree::DispatchStrategy::NfaTryAll { rule_labels, .. } => rule_labels,
        crate::decision_tree::DispatchStrategy::DisjointSuffix { suffix_map, .. } => {
            suffix_map.values().cloned().collect()
        }
        _ => Vec::new(),
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// G10: Ambiguous Associativity
// ══════════════════════════════════════════════════════════════════════════════

fn lint_g10_ambiguous_associativity(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let category_names: Vec<String> = ctx.categories.iter().map(|c| c.name.clone()).collect();

    for cat in &category_names {
        let ops = ctx.bp_table.operators_for_category(cat);

        // Group by left_bp (same precedence level)
        let mut bp_to_ops: HashMap<u8, Vec<&crate::binding_power::InfixOperator>> = HashMap::new();
        for op in &ops {
            bp_to_ops.entry(op.left_bp).or_default().push(op);
        }

        for (left_bp, group) in &bp_to_ops {
            if group.len() < 2 {
                continue;
            }

            let first_assoc = group[0].associativity();
            let has_mixed = group.iter().any(|op| op.associativity() != first_assoc);
            if has_mixed {
                let op_names: Vec<&str> = group.iter().map(|op| op.terminal.as_str()).collect();
                diagnostics.push(LintDiagnostic {
                    id: "G10",
                    name: "ambiguous-associativity",
                    severity: LintSeverity::Warning,
                    category: Some(cat.clone()),
                    rule: None,
                    message: format!(
                        "same-precedence operators [{}] in category `{}` (left_bp={}) \
                         have different associativity",
                        op_names.join(", "),
                        cat,
                        left_bp,
                    ),
                    hint: Some(
                        "use explicit precedence levels to separate operators with \
                         different associativity"
                            .to_string(),
                    ),
                    grammar_name: Some(ctx.grammar_name.to_string()),
                    source_location: None,
                });
            }
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// W01: Dead Rule (migrated from pipeline.rs)
// ══════════════════════════════════════════════════════════════════════════════

fn lint_w01_dead_rule(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    // Use pre-computed dead-rule warnings from the pipeline (cached in LintContext).
    // This avoids re-invoking detect_dead_rules() which was previously called 3x
    // with identical inputs.
    //
    // A4 (inter-category dead-path) and A8 (nearly-dead path) are still computed
    // here because they are lint-only analyses not needed by the pipeline codegen.
    let mut warnings: Vec<crate::pipeline::DeadRuleWarning> =
        ctx.dead_rule_warnings.to_vec();

    // A4: Inter-category dead-path detection via forward-backward analysis
    // on an undirected inter-category graph including all syntax references
    // (NonTerminal, Binder, Collection). See also G08 which checks directed
    // cast-graph reachability specifically. G08 fires on categories without
    // a directed cast path to the primary; A4 fires on categories structurally
    // isolated via the richer undirected graph. The two are complementary.
    let inter_cat_warnings = crate::pipeline::detect_inter_category_dead_paths(
        ctx.rules,
        ctx.categories,
        ctx.first_sets,
        ctx.all_syntax,
    );
    // Only add inter-category warnings for rules not already flagged by Tier 1-3
    let existing_rules: std::collections::HashSet<String> = warnings
        .iter()
        .map(|w| match w {
            crate::pipeline::DeadRuleWarning::LiteralNoNativeType { rule_label, .. }
            | crate::pipeline::DeadRuleWarning::UnreachableCategory { rule_label, .. }
            | crate::pipeline::DeadRuleWarning::WfstUnreachable { rule_label, .. }
            | crate::pipeline::DeadRuleWarning::InterCategoryDeadPath { rule_label, .. }
            | crate::pipeline::DeadRuleWarning::NearlyDeadPath { rule_label, .. } => {
                rule_label.clone()
            }
        })
        .collect();
    for w in inter_cat_warnings {
        match &w {
            crate::pipeline::DeadRuleWarning::InterCategoryDeadPath { rule_label, .. } => {
                if !existing_rules.contains(rule_label) {
                    warnings.push(w);
                }
            }
            _ => warnings.push(w),
        }
    }

    // A8: Nearly-dead inter-category path detection via ProductWeight<BooleanWeight, CountingWeight>.
    // Only flags rules whose categories are reachable (not already flagged by A4) but have
    // very few derivation paths relative to the total (< 1% of max count).
    let nearly_dead_warnings = crate::pipeline::detect_nearly_dead_paths(
        ctx.rules,
        ctx.categories,
        ctx.first_sets,
        ctx.all_syntax,
    );
    // Collect all already-flagged rules to avoid duplicate diagnostics
    let all_flagged: std::collections::HashSet<String> = warnings
        .iter()
        .map(|w| match w {
            crate::pipeline::DeadRuleWarning::LiteralNoNativeType { rule_label, .. }
            | crate::pipeline::DeadRuleWarning::UnreachableCategory { rule_label, .. }
            | crate::pipeline::DeadRuleWarning::WfstUnreachable { rule_label, .. }
            | crate::pipeline::DeadRuleWarning::InterCategoryDeadPath { rule_label, .. }
            | crate::pipeline::DeadRuleWarning::NearlyDeadPath { rule_label, .. } => {
                rule_label.clone()
            }
        })
        .collect();
    for w in nearly_dead_warnings {
        if let crate::pipeline::DeadRuleWarning::NearlyDeadPath { ref rule_label, .. } = w {
            if !all_flagged.contains(rule_label) {
                warnings.push(w);
            }
        }
    }

    for w in &warnings {
        let (rule_label, category, hint_msg) = match &w {
            crate::pipeline::DeadRuleWarning::LiteralNoNativeType {
                rule_label,
                category,
            } => (
                rule_label.clone(),
                category.clone(),
                "add a native_type to the category or remove the literal rule",
            ),
            crate::pipeline::DeadRuleWarning::UnreachableCategory {
                rule_label,
                category,
            } => (
                rule_label.clone(),
                category.clone(),
                "add a prefix rule to make the category reachable",
            ),
            crate::pipeline::DeadRuleWarning::WfstUnreachable {
                rule_label,
                category,
            } => (
                rule_label.clone(),
                category.clone(),
                "remove the rule or add a unique dispatch token",
            ),
            crate::pipeline::DeadRuleWarning::InterCategoryDeadPath {
                rule_label,
                category,
                ..
            } => (
                rule_label.clone(),
                category.clone(),
                "check inter-category connections; this category may be isolated",
            ),
            crate::pipeline::DeadRuleWarning::NearlyDeadPath {
                rule_label,
                category,
                ..
            } => (
                rule_label.clone(),
                category.clone(),
                "this category has very few derivation paths; consider simplifying or removing rules",
            ),
        };

        // A8: NearlyDeadPath gets its own lint ID (W07, note-level) since the rule is
        // technically reachable — this is a diagnostic hint, not a dead-code warning.
        let (lint_id, lint_name, severity) = match &w {
            crate::pipeline::DeadRuleWarning::NearlyDeadPath { .. } => {
                ("W07", "nearly-dead-path", LintSeverity::Note)
            }
            _ => ("W01", "dead-rule", LintSeverity::Warning),
        };

        diagnostics.push(LintDiagnostic {
            id: lint_id,
            name: lint_name,
            severity,
            category: Some(category.clone()),
            rule: Some(rule_label.clone()),
            message: format!("{}", w),
            hint: Some(hint_msg.to_string()),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: ctx.rule_locations.get(&(rule_label.clone(), category.clone())).copied(),
        });
    }

    // Dead prefix detection: use the shared detect_dead_prefixes() function
    // (also used by the pipeline to increase recovery WFST weights).
    let dead_prefixes = crate::pipeline::detect_dead_prefixes(
        &warnings, ctx.decision_trees, ctx.token_id_map,
    );
    for (cat_name, prefix_tokens) in &dead_prefixes {
        for token_variant in prefix_tokens {
            // Look up which rules this prefix reaches, for the diagnostic message
            if let Some(tree) = ctx.decision_trees.get(cat_name) {
                let strategy = tree.dispatch_strategy(token_variant, ctx.token_id_map);
                let rule_labels = match &strategy {
                    crate::decision_tree::DispatchStrategy::Singleton { rule_label } => {
                        vec![rule_label.clone()]
                    }
                    crate::decision_tree::DispatchStrategy::NfaTryAll { rule_labels, .. } => {
                        rule_labels.clone()
                    }
                    crate::decision_tree::DispatchStrategy::DisjointSuffix { suffix_map, .. } => {
                        suffix_map.values().cloned().collect()
                    }
                    crate::decision_tree::DispatchStrategy::NotPresent => Vec::new(),
                };
                diagnostics.push(LintDiagnostic {
                    id: "W01",
                    name: "dead-prefix",
                    severity: LintSeverity::Note,
                    category: Some(cat_name.clone()),
                    rule: None,
                    message: format!(
                        "prefix `{}` in category `{}` leads only to dead rules [{}]; \
                         entire prefix subtrie is unreachable",
                        token_variant,
                        cat_name,
                        rule_labels.join(", "),
                    ),
                    hint: Some(
                        "all rules reachable from this prefix are dead — \
                         the dispatch arm is unreachable"
                            .to_string(),
                    ),
                    grammar_name: Some(ctx.grammar_name.to_string()),
                    source_location: None,
                });
            }
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// W02: NFA Ambiguous Prefix (migrated from pipeline.rs)
// ══════════════════════════════════════════════════════════════════════════════

fn lint_w02_nfa_ambiguous_prefix(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    for cat_name in ctx.nfa_spillover_categories {
        let rd_by_token = crate::trampoline::group_rd_by_dispatch_token_pub(ctx.rd_rules, cat_name);
        if let Some(wfst) = ctx.prediction_wfsts.get(cat_name.as_str()) {
            for (token, rules) in &rd_by_token {
                if rules.len() <= 1 {
                    continue;
                }
                let labels: Vec<&str> = rules.iter().map(|r| r.label.as_str()).collect();
                let ordered = wfst.nfa_alternative_order(token, &labels);
                let weights: Vec<f64> = ordered.iter().map(|(_, w)| w.0).collect();
                let all_equal =
                    weights.windows(2).all(|w| (w[0] - w[1]).abs() < 1e-12);

                // Sprint 4: Compute ContextWeight narrowing for this dispatch token.
                // If the WFST has context labels, report the narrowed count.
                let (_ctx_narrowed, narrowed_count) = wfst.context_narrowing(&[token]);
                let original_count = rules.len();

                let mut message = format!(
                    "ambiguous prefix dispatch for token `{}` in category `{}`: \
                     rules [{}] all match",
                    token,
                    cat_name,
                    labels.join(", "),
                );

                if narrowed_count > 0 && (narrowed_count as usize) < original_count {
                    message.push_str(&format!(
                        " (ContextWeight narrows to {}/{} candidates)",
                        narrowed_count, original_count,
                    ));
                }

                if all_equal {
                    message.push_str(&format!(
                        " — all {} alternatives have equal weight ({:.1}); \
                         resolution deferred to semantic disambiguation",
                        original_count,
                        weights.first().copied().unwrap_or(0.5),
                    ));
                }

                // When ContextWeight narrows to singleton, downgrade to Note
                let severity = if narrowed_count == 1 {
                    LintSeverity::Note
                } else {
                    LintSeverity::Warning
                };

                diagnostics.push(LintDiagnostic {
                    id: "W02",
                    name: "nfa-ambiguous-prefix",
                    severity,
                    category: Some(cat_name.clone()),
                    rule: None,
                    message,
                    hint: Some(
                        "add distinguishing syntax or assign different WFST weights \
                         to resolve the ambiguity"
                            .to_string(),
                    ),
                    grammar_name: Some(ctx.grammar_name.to_string()),
                    source_location: None,
                });
            }
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// W03: High Ambiguity Token
// ══════════════════════════════════════════════════════════════════════════════

fn lint_w03_high_ambiguity_token(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let category_names: Vec<String> = ctx.categories.iter().map(|c| c.name.clone()).collect();

    for cat in &category_names {
        if let Some(wfst) = ctx.prediction_wfsts.get(cat.as_str()) {
            if let Some(first_set) = ctx.first_sets.get(cat) {
                for token in first_set.sorted_tokens() {
                    let predictions = wfst.predict_with_confidence(&token);
                    if let Some((_, count_weight)) = predictions.first() {
                        if count_weight.count() >= 3 {
                            let action_labels: Vec<String> = predictions
                                .iter()
                                .map(|(a, _)| a.action.rule_label().to_string())
                                .collect();
                            diagnostics.push(LintDiagnostic {
                                id: "W03",
                                name: "high-ambiguity-token",
                                severity: LintSeverity::Warning,
                                category: Some(cat.clone()),
                                rule: None,
                                message: format!(
                                    "token `{}` dispatches to {} rules in category `{}`: [{}]",
                                    token,
                                    predictions.len(),
                                    cat,
                                    action_labels.join(", "),
                                ),
                                hint: Some(
                                    "high branching factor — consider adding unique \
                                     dispatch tokens to reduce ambiguity"
                                        .to_string(),
                                ),
                                grammar_name: Some(ctx.grammar_name.to_string()),
                                source_location: None,
                            });
                        }
                    }
                }
            }
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// W04: Weight Gap Anomaly
// ══════════════════════════════════════════════════════════════════════════════

fn lint_w04_weight_gap_anomaly(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let category_names: Vec<String> = ctx.categories.iter().map(|c| c.name.clone()).collect();

    for cat in &category_names {
        if let Some(wfst) = ctx.prediction_wfsts.get(cat.as_str()) {
            if let Some(first_set) = ctx.first_sets.get(cat) {
                for token in first_set.sorted_tokens() {
                    let actions = wfst.predict(&token);
                    if actions.len() >= 2 {
                        let best = actions[0].weight.value();
                        let second = actions[1].weight.value();
                        let gap = second - best;

                        if gap > 5.0 {
                            diagnostics.push(LintDiagnostic {
                                id: "W04",
                                name: "weight-gap-anomaly",
                                severity: LintSeverity::Note,
                                category: Some(cat.clone()),
                                rule: None,
                                message: format!(
                                    "token `{}` in category `{}`: gap of {:.1} between best \
                                     rule `{}` (weight {:.1}) and second-best `{}` (weight {:.1}) \
                                     — near-deterministic treated as ambiguous",
                                    token,
                                    cat,
                                    gap,
                                    actions[0].action.rule_label(),
                                    best,
                                    actions[1].action.rule_label(),
                                    second,
                                ),
                                hint: Some(
                                    "the large weight gap suggests this token is effectively \
                                     unambiguous — the second alternative is very unlikely"
                                        .to_string(),
                                ),
                                grammar_name: Some(ctx.grammar_name.to_string()),
                                source_location: None,
                            });
                        }
                    }
                }
            }
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// W06: Weight Inversion
// ══════════════════════════════════════════════════════════════════════════════

fn lint_w06_weight_inversion(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    // Build a map from rule label → syntax item count (specificity)
    let specificity: HashMap<&str, usize> = ctx
        .all_syntax
        .iter()
        .map(|(label, _, syntax)| (label.as_str(), syntax.len()))
        .collect();

    let category_names: Vec<String> = ctx.categories.iter().map(|c| c.name.clone()).collect();

    for cat in &category_names {
        if let Some(wfst) = ctx.prediction_wfsts.get(cat.as_str()) {
            if let Some(first_set) = ctx.first_sets.get(cat) {
                for token in first_set.sorted_tokens() {
                    let actions = wfst.predict(&token);
                    // Check each pair: if less-specific rule has lower weight (better)
                    // than more-specific rule, that's an inversion
                    for i in 0..actions.len() {
                        for j in (i + 1)..actions.len() {
                            let label_i = actions[i].action.rule_label();
                            let label_j = actions[j].action.rule_label();
                            let spec_i = specificity.get(label_i.as_str()).copied().unwrap_or(0);
                            let spec_j = specificity.get(label_j.as_str()).copied().unwrap_or(0);
                            let w_i = actions[i].weight.value();
                            let w_j = actions[j].weight.value();

                            // Inversion: less-specific (lower spec) has lower weight (better priority)
                            // than more-specific (higher spec)
                            if spec_i < spec_j && w_i < w_j {
                                diagnostics.push(LintDiagnostic {
                                    id: "W06",
                                    name: "weight-inversion",
                                    severity: LintSeverity::Note,
                                    category: Some(cat.clone()),
                                    rule: None,
                                    message: format!(
                                        "weight inversion for token `{}` in category `{}`: \
                                         less-specific rule `{}` ({} items, weight {:.2}) has \
                                         better priority than more-specific `{}` ({} items, \
                                         weight {:.2})",
                                        token, cat, label_i, spec_i, w_i, label_j, spec_j, w_j,
                                    ),
                                    hint: Some(
                                        "more-specific rules should typically have lower \
                                         (better) weights — check rule ordering or WFST weights"
                                            .to_string(),
                                    ),
                                    grammar_name: Some(ctx.grammar_name.to_string()),
                                    source_location: None,
                                });
                            }
                        }
                    }
                }
            }
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// W10: Spillover Eliminable by Lookahead (Sprint 6)
// ══════════════════════════════════════════════════════════════════════════════

/// W10: For each NFA-spillover category, compute minimum k such that k-token
/// lookahead eliminates try-all. Emits Note with required depth when all
/// branches narrow to singletons at depth ≤ 4.
fn lint_w10_spillover_eliminable_by_lookahead(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    for cat_name in ctx.nfa_spillover_categories {
        if let Some(wfst) = ctx.prediction_wfsts.get(cat_name.as_str()) {
            if wfst.context_labels.is_empty() {
                continue;
            }

            let rd_by_token = crate::trampoline::group_rd_by_dispatch_token_pub(
                ctx.rd_rules, cat_name,
            );

            for (token, rules) in &rd_by_token {
                if rules.len() <= 1 {
                    continue;
                }

                // Check if two-token lookahead resolves this group
                if let Some(label) = wfst.is_deterministic_context(&[token]) {
                    diagnostics.push(LintDiagnostic {
                        id: "W10",
                        name: "spillover-eliminable-by-lookahead",
                        severity: LintSeverity::Note,
                        category: Some(cat_name.clone()),
                        rule: None,
                        message: format!(
                            "NFA spillover for token `{}` in `{}` could be eliminated \
                             with 1-token lookahead (resolves to `{}`)",
                            token, cat_name, label,
                        ),
                        hint: Some(
                            "two-token WFST disambiguation resolves this group \
                             deterministically"
                                .to_string(),
                        ),
                        grammar_name: Some(ctx.grammar_name.to_string()),
                        source_location: None,
                    });
                } else {
                    // Check two-token narrowing
                    let (_, count) = wfst.context_narrowing(&[token]);
                    if count > 0 && (count as usize) < rules.len() {
                        diagnostics.push(LintDiagnostic {
                            id: "W10",
                            name: "spillover-eliminable-by-lookahead",
                            severity: LintSeverity::Note,
                            category: Some(cat_name.clone()),
                            rule: None,
                            message: format!(
                                "NFA spillover for token `{}` in `{}` narrows from {} to {} \
                                 candidates with ContextWeight analysis",
                                token, cat_name, rules.len(), count,
                            ),
                            hint: Some(
                                "consider extending lookahead depth to further reduce \
                                 ambiguity"
                                    .to_string(),
                            ),
                            grammar_name: Some(ctx.grammar_name.to_string()),
                            source_location: None,
                        });
                    }
                }
            }
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// W11: Context Narrowing Deterministic (Sprint 6)
// ══════════════════════════════════════════════════════════════════════════════

/// W11: When ContextWeight narrows to singleton, suggest replacing NfaTryAll
/// with Commit dispatch.
fn lint_w11_context_narrowing_deterministic(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    for (cat_name, tree) in ctx.decision_trees {
        if let Some(wfst) = ctx.prediction_wfsts.get(cat_name.as_str()) {
            if wfst.context_labels.is_empty() {
                continue;
            }

            // Get all dispatch tokens for this category
            let first_set = match ctx.first_sets.get(cat_name) {
                Some(fs) => fs,
                None => continue,
            };

            for token in first_set.sorted_tokens() {
                let variant = crate::automata::codegen::terminal_to_variant_name(&token);
                let strategy = tree.dispatch_strategy(&variant, ctx.token_id_map);

                if let crate::decision_tree::DispatchStrategy::NfaTryAll {
                    rule_labels, ..
                } = &strategy
                {
                    if let Some(label) = wfst.is_deterministic_context(&[&token]) {
                        diagnostics.push(LintDiagnostic {
                            id: "W11",
                            name: "context-narrowing-deterministic",
                            severity: LintSeverity::Note,
                            category: Some(cat_name.clone()),
                            rule: None,
                            message: format!(
                                "NfaTryAll for token `{}` in `{}` ({} candidates) is \
                                 deterministic via ContextWeight — resolves to `{}`",
                                token, cat_name, rule_labels.len(), label,
                            ),
                            hint: Some(
                                "the NFA try-all could be replaced with direct Commit \
                                 dispatch for this token"
                                    .to_string(),
                            ),
                            grammar_name: Some(ctx.grammar_name.to_string()),
                            source_location: None,
                        });
                    }
                }
            }
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// W12: Training Would Improve (Sprint 6, wfst-log gated)
// ══════════════════════════════════════════════════════════════════════════════

/// W12: Compute Shannon entropy at each dispatch point. High entropy suggests
/// training would improve weight assignment.
#[cfg(feature = "wfst-log")]
fn lint_w12_training_would_improve(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    for (cat_name, wfst) in ctx.prediction_wfsts {
        let (entropy_nats, entropy_bits) = wfst.compute_entropy();

        // High entropy threshold: > 2.0 bits (near-uniform distribution)
        if entropy_bits > 2.0 {
            let num_actions = wfst.num_actions();
            diagnostics.push(LintDiagnostic {
                id: "W12",
                name: "training-would-improve",
                severity: LintSeverity::Note,
                category: Some(cat_name.clone()),
                rule: None,
                message: format!(
                    "category `{}` has high dispatch entropy ({:.2} bits, {:.2} nats) \
                     across {} actions — WFST weight training would likely improve \
                     disambiguation quality",
                    cat_name, entropy_bits, entropy_nats, num_actions,
                ),
                hint: Some(
                    "use `SpilloverTrainer` or `train_from_corrections()` to \
                     learn better weights from parse examples"
                        .to_string(),
                ),
                grammar_name: Some(ctx.grammar_name.to_string()),
                source_location: None,
            });
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// W13: WPDS-Unreachable Rule (stack-aware dead-rule verification)
// ══════════════════════════════════════════════════════════════════════════════

/// W13: WPDS stack-aware dead-rule detection.
///
/// Uses poststar saturation results to identify rules that are unreachable
/// when stack context (call/return matching) is considered. This is strictly
/// more precise than the finite-state W01 tier: a rule may be reachable in
/// the WFST projection but unreachable in the WPDS because no valid calling
/// context exists.
fn lint_w13_wpds_unreachable(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let analysis = match ctx.wpds_analysis {
        Some(a) => a,
        None => return,
    };

    for unreachable in &analysis.unreachable_rules {
        let missing_ctx = if unreachable.missing_contexts.is_empty() {
            String::new()
        } else {
            format!(
                " (missing callers: {})",
                unreachable.missing_contexts.join(", ")
            )
        };

        // D15: Append witness trace if available
        let witness = if unreachable.witness_trace.is_empty() {
            String::new()
        } else {
            format!(
                "\n  witness trace:\n    {}",
                unreachable.witness_trace.join("\n    ")
            )
        };

        let source_location = ctx
            .rule_locations
            .get(&(unreachable.rule_label.clone(), unreachable.category.clone()))
            .copied();

        diagnostics.push(LintDiagnostic {
            id: "W13",
            name: "wpds-unreachable",
            severity: LintSeverity::Warning,
            category: Some(unreachable.category.clone()),
            rule: Some(unreachable.rule_label.clone()),
            message: format!(
                "rule `{}` in category `{}` is unreachable via WPDS stack-aware analysis{}{}",
                unreachable.rule_label, unreachable.category, missing_ctx, witness,
            ),
            hint: Some(
                "this rule's category is not reachable from the root via any \
                 valid call/return path; consider adding a cross-category \
                 reference or removing the rule"
                    .to_string(),
            ),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location,
        });
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// D14: WPDS Complexity Report
// ══════════════════════════════════════════════════════════════════════════════

/// Emit an Info diagnostic summarizing WPDS analysis complexity:
/// `|Γ|` (stack symbols), `|Δ|` (rules), SCC count, reachable categories.
fn lint_d14_wpds_complexity_report(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let analysis = match ctx.wpds_analysis {
        Some(a) => a,
        None => return,
    };

    let scc_count = analysis.call_graph.sccs.len();
    let nontrivial_sccs: Vec<_> = analysis
        .call_graph
        .sccs
        .iter()
        .filter(|scc| {
            scc.len() > 1
                || (scc.len() == 1
                    && analysis
                        .call_graph
                        .edges
                        .iter()
                        .any(|e| e.caller_cat == scc[0] && e.callee_cat == scc[0]))
        })
        .collect();

    let edge_count = analysis.call_graph.edges.len();
    let reachable = analysis.reachable_categories.len();
    let total_cats = analysis.call_graph.categories.len();

    let cycle_count = analysis.cycles.len();
    let recursive_cats: usize = analysis
        .depth_bounds
        .values()
        .filter(|db| db.is_recursive)
        .count();

    let mut msg = format!(
        "WPDS analysis: |Γ|={}, |Δ|={}, {} SCCs, {} call edges, {}/{} reachable categories, {} cycles, {} recursive",
        analysis.num_symbols, analysis.num_rules, scc_count, edge_count, reachable, total_cats,
        cycle_count, recursive_cats,
    );

    if !nontrivial_sccs.is_empty() {
        let scc_desc: Vec<String> = nontrivial_sccs
            .iter()
            .map(|scc| format!("{{{}}}", scc.join(", ")))
            .collect();
        msg.push_str(&format!(
            "; recursive SCCs: {}",
            scc_desc.join(", ")
        ));
    }

    // Include depth bounds summary
    let bounded: Vec<_> = analysis
        .depth_bounds
        .iter()
        .filter(|(_, db)| db.max_depth.is_some())
        .map(|(cat, db)| format!("{}={}", cat, db.max_depth.expect("filtered")))
        .collect();
    if !bounded.is_empty() {
        msg.push_str(&format!("; max_depth: {}", bounded.join(", ")));
    }

    diagnostics.push(LintDiagnostic {
        id: "D14",
        name: "wpds-complexity-report",
        severity: LintSeverity::Info,
        category: None,
        rule: None,
        message: msg,
        hint: None,
        grammar_name: Some(ctx.grammar_name.to_string()),
        source_location: None,
    });
}

// ══════════════════════════════════════════════════════════════════════════════
// P05: WPDS Pipeline Cost Report
// ══════════════════════════════════════════════════════════════════════════════

/// Emit an Info diagnostic reporting WPDS analysis wall-clock time.
fn lint_p05_wpds_pipeline_cost(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let elapsed = match ctx.wpds_elapsed {
        Some(d) => d,
        None => return,
    };

    let analysis = match ctx.wpds_analysis {
        Some(a) => a,
        None => return,
    };

    diagnostics.push(LintDiagnostic {
        id: "P05",
        name: "wpds-pipeline-cost",
        severity: LintSeverity::Info,
        category: None,
        rule: None,
        message: format!(
            "WPDS analysis completed in {:.2}ms (|Γ|={}, |Δ|={}, {} unreachable rules)",
            elapsed.as_secs_f64() * 1000.0,
            analysis.num_symbols,
            analysis.num_rules,
            analysis.unreachable_rules.len(),
        ),
        hint: None,
        grammar_name: Some(ctx.grammar_name.to_string()),
        source_location: None,
    });
}

// ══════════════════════════════════════════════════════════════════════════════
// W14: WPDS-Confirmed Ambiguity
// ══════════════════════════════════════════════════════════════════════════════

/// Warning when WPDS analysis confirms genuine pushdown-level ambiguity for
/// NFA dispatch tokens, distinguishing from WFST false-positives.
///
/// Uses the WPDS stringsum parse count for categories with NFA spillover:
/// `CountingWeight > 1` at the pushdown level confirms true ambiguity.
fn lint_w14_wpds_confirmed_ambiguity(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let analysis = match ctx.wpds_analysis {
        Some(a) => a,
        None => return,
    };

    // For each NFA spillover category, check if WPDS confirms the ambiguity.
    // If a category is in nfa_spillover but NOT reachable in WPDS, the ambiguity
    // is a WFST-level false positive.
    for cat in ctx.nfa_spillover_categories {
        if !analysis.reachable_categories.contains(cat) {
            // Category is WPDS-unreachable → the ambiguity is a false positive
            diagnostics.push(LintDiagnostic {
                id: "W14",
                name: "wpds-confirmed-ambiguity",
                severity: LintSeverity::Note,
                category: Some(cat.clone()),
                rule: None,
                message: format!(
                    "NFA spillover for `{}` may be a WFST false-positive \
                     (category is WPDS-unreachable)",
                    cat,
                ),
                hint: Some(
                    "WPDS stack-aware analysis suggests this category is unreachable; \
                     the NFA ambiguity may not manifest in practice"
                        .to_string(),
                ),
                grammar_name: Some(ctx.grammar_name.to_string()),
                source_location: None,
            });
        } else {
            // Category is reachable — check if multiple rules share the
            // same calling context (confirmed pushdown ambiguity).
            // We check if the call graph fan-in > 1 for this category,
            // which means multiple callers can reach it (different stack configs).
            let fan_in = analysis
                .call_graph
                .fan_in
                .get(cat)
                .copied()
                .unwrap_or(0);
            let calling_context_count = analysis
                .calling_contexts
                .get(cat)
                .map(|c| c.len())
                .unwrap_or(0);

            if fan_in > 0 && calling_context_count > 1 {
                diagnostics.push(LintDiagnostic {
                    id: "W14",
                    name: "wpds-confirmed-ambiguity",
                    severity: LintSeverity::Warning,
                    category: Some(cat.clone()),
                    rule: None,
                    message: format!(
                        "NFA spillover for `{}` is confirmed at pushdown level \
                         ({} calling contexts, fan-in={})",
                        cat, calling_context_count, fan_in,
                    ),
                    hint: Some(
                        "the ambiguity is genuine: multiple stack configurations \
                         can reach this category's dispatch point"
                            .to_string(),
                    ),
                    grammar_name: Some(ctx.grammar_name.to_string()),
                    source_location: None,
                });
            }
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// COMP-08: Grammar Refactoring Suggestions
// ══════════════════════════════════════════════════════════════════════════════

/// Emit Note-level suggestions for grammar restructuring based on WPDS analysis.
///
/// Heuristics from G33/G34/G35/G36:
/// - High fan-in AND fan-out (>5 each) → suggest splitting hub category
/// - Fan-in=1, ≤3 rules, fan-out=0 → suggest inlining (J03 candidate)
/// - SCC with >2 members → suggest cycle-breaking via intermediate category
/// - Single calling context → suggest moving rule to caller category
fn lint_comp08_refactoring_suggestions(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let analysis = match ctx.wpds_analysis {
        Some(a) => a,
        None => return,
    };

    let cg = &analysis.call_graph;

    // Hub detection: high fan-in AND fan-out
    for cat in &cg.categories {
        let fi = cg.fan_in.get(cat).copied().unwrap_or(0);
        let fo = cg.fan_out.get(cat).copied().unwrap_or(0);
        if fi > 5 && fo > 5 {
            diagnostics.push(LintDiagnostic {
                id: "COMP-08",
                name: "wpds-refactoring-suggestion",
                severity: LintSeverity::Note,
                category: Some(cat.clone()),
                rule: None,
                message: format!(
                    "category `{}` is a hub (fan-in={}, fan-out={}); \
                     consider splitting into smaller categories",
                    cat, fi, fo,
                ),
                hint: Some(
                    "hub categories can cause cascading ambiguity; splitting \
                     may improve dispatch determinism and parse performance"
                        .to_string(),
                ),
                grammar_name: Some(ctx.grammar_name.to_string()),
                source_location: None,
            });
        }
    }

    // Inline candidate: fan-in=1, ≤3 rules, fan-out=0
    for cat in &cg.categories {
        let fi = cg.fan_in.get(cat).copied().unwrap_or(0);
        let fo = cg.fan_out.get(cat).copied().unwrap_or(0);
        let rule_count = ctx
            .rules
            .iter()
            .filter(|r| r.category == *cat)
            .count();

        if fi == 1 && rule_count <= 3 && fo == 0 {
            // Find the sole caller
            let caller = cg
                .edges
                .iter()
                .find(|e| e.callee_cat == *cat)
                .map(|e| e.caller_cat.as_str())
                .unwrap_or("unknown");

            diagnostics.push(LintDiagnostic {
                id: "COMP-08",
                name: "wpds-refactoring-suggestion",
                severity: LintSeverity::Note,
                category: Some(cat.clone()),
                rule: None,
                message: format!(
                    "category `{}` has 1 caller (`{}`), {} rules, no outgoing calls; \
                     consider inlining into `{}`",
                    cat, caller, rule_count, caller,
                ),
                hint: Some(
                    "inlining small leaf categories eliminates cross-category \
                     Push/Pop overhead in the WPDS and simplifies the call graph"
                        .to_string(),
                ),
                grammar_name: Some(ctx.grammar_name.to_string()),
                source_location: None,
            });
        }
    }

    // Large SCC: >2 members → suggest cycle-breaking
    for cycle in &analysis.cycles {
        if cycle.categories.len() > 2 {
            diagnostics.push(LintDiagnostic {
                id: "COMP-08",
                name: "wpds-refactoring-suggestion",
                severity: LintSeverity::Note,
                category: None,
                rule: None,
                message: format!(
                    "mutual recursion cycle with {} categories: {{{}}}; \
                     consider introducing an intermediate category to break the cycle",
                    cycle.categories.len(),
                    cycle.categories.join(", "),
                ),
                hint: Some(
                    "large mutual-recursion cycles increase WPDS saturation time \
                     and can obscure dead-rule detection"
                        .to_string(),
                ),
                grammar_name: Some(ctx.grammar_name.to_string()),
                source_location: None,
            });
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// W16: WPDS Weight Inversion Across Contexts
// ══════════════════════════════════════════════════════════════════════════════

/// Warning when WPDS-derived optimal weight order contradicts WFST dispatch weight.
///
/// If rule A has lower WFST weight (higher priority) than rule B, but WPDS
/// shows B is more reachable across stack contexts, this is a weight inversion.
fn lint_w16_wpds_weight_inversion(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let analysis = match ctx.wpds_analysis {
        Some(a) => a,
        None => return,
    };

    for (cat, wfst) in ctx.prediction_wfsts {
        // Get WPDS weight for this category
        let wpds_cat_weight = analysis.category_weights.get(cat).copied();
        if wpds_cat_weight.is_none() {
            continue;
        }

        // Check pairs of actions for inversions: WFST says A < B but WPDS says B < A
        // We compare using the WPDS calling context weights for each rule's category.
        // If the rule's own category has a lower WPDS weight than other rules' categories,
        // but WFST gives it a higher weight, that's an inversion.
        for i in 0..wfst.actions.len() {
            for j in (i + 1)..wfst.actions.len() {
                let a = &wfst.actions[i];
                let b = &wfst.actions[j];

                // Only compare if they share a category (same dispatch context)
                let a_label = a.action.rule_label();
                let b_label = b.action.rule_label();

                // Check if WFST weight order disagrees with WPDS weight
                let wfst_a_better = a.weight.value() < b.weight.value();
                let wpds_a_weight = analysis.category_weights.get(cat).copied().unwrap_or(f64::INFINITY);
                let wpds_b_weight = wpds_a_weight; // Same category, but we need per-rule weights

                // Per-rule WPDS weight check: use calling contexts if available
                let a_context_count = analysis
                    .calling_contexts
                    .get(cat)
                    .map(|ctxs| ctxs.len())
                    .unwrap_or(0);

                // Only flag inversions when we have meaningful weight differences
                if wfst_a_better
                    && a.weight.value() + 1.0 < b.weight.value()
                    && a_context_count > 0
                    && wpds_a_weight > wpds_b_weight + 0.5
                {
                    diagnostics.push(LintDiagnostic {
                        id: "W16",
                        name: "wpds-weight-inversion",
                        severity: LintSeverity::Warning,
                        category: Some(cat.clone()),
                        rule: Some(a_label.clone()),
                        message: format!(
                            "rule `{}` has WFST weight {:.1} but WPDS weight {:.1} — \
                             consider reordering (WPDS suggests `{}` is more reachable)",
                            a_label,
                            a.weight.value(),
                            wpds_a_weight,
                            b_label,
                        ),
                        hint: Some(
                            "WPDS stack-aware analysis suggests a different optimal dispatch \
                             order than the WFST prediction weights"
                                .to_string(),
                        ),
                        grammar_name: Some(ctx.grammar_name.to_string()),
                        source_location: None,
                    });
                }
            }
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// R01: Empty Sync Set
// ══════════════════════════════════════════════════════════════════════════════

fn lint_r01_empty_sync_set(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    for rwfst in ctx.recovery_wfsts {
        if rwfst.sync_tokens().is_empty() {
            // Suggest good sync token candidates from the decision tree
            let suggestion = suggest_sync_tokens_from_trie(ctx, rwfst.category());
            let hint = if suggestion.is_empty() {
                "add structural delimiters or ensure the category has FOLLOW set tokens"
                    .to_string()
            } else {
                format!(
                    "add structural delimiters or FOLLOW set tokens. \
                     Decision tree suggests shallow tokens: [{}]",
                    suggestion,
                )
            };

            diagnostics.push(LintDiagnostic {
                id: "R01",
                name: "empty-sync-set",
                severity: LintSeverity::Warning,
                category: Some(rwfst.category().to_string()),
                rule: None,
                message: format!(
                    "category `{}` has no sync tokens — recovery always skips to EOF",
                    rwfst.category(),
                ),
                hint: Some(hint),
                grammar_name: Some(ctx.grammar_name.to_string()),
                source_location: None,
            });
        }
    }
}

/// Suggest sync token candidates based on trie depth (shallower = better recovery target).
fn suggest_sync_tokens_from_trie(ctx: &LintContext, category: &str) -> String {
    let tree = match ctx.decision_trees.get(category) {
        Some(t) => t,
        None => return String::new(),
    };
    let dispatch_tokens = tree.dispatch_tokens(ctx.token_id_map);
    // Tokens at depth 0 (direct root children) are excellent sync targets
    let mut shallow_tokens: Vec<String> = Vec::new();
    for token_variant in &dispatch_tokens {
        let strategy = tree.dispatch_strategy(token_variant, ctx.token_id_map);
        match strategy {
            crate::decision_tree::DispatchStrategy::Singleton { .. } => {
                shallow_tokens.push(token_variant.clone());
            }
            _ => {}
        }
    }
    shallow_tokens.sort();
    shallow_tokens.truncate(5);
    shallow_tokens.join(", ")
}

// ══════════════════════════════════════════════════════════════════════════════
// R02: Sparse Recovery
// ══════════════════════════════════════════════════════════════════════════════

fn lint_r02_sparse_recovery(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    for rwfst in ctx.recovery_wfsts {
        let count = rwfst.sync_tokens().len();
        if count > 0 && count < 2 {
            // Assess sync token quality via decision tree depth
            let quality_notes = assess_sync_quality(ctx, rwfst);

            let hint = if quality_notes.is_empty() {
                "add more structural delimiters to improve error recovery quality"
                    .to_string()
            } else {
                format!(
                    "add more structural delimiters to improve error recovery quality. {}",
                    quality_notes,
                )
            };

            diagnostics.push(LintDiagnostic {
                id: "R02",
                name: "sparse-recovery",
                severity: LintSeverity::Note,
                category: Some(rwfst.category().to_string()),
                rule: None,
                message: format!(
                    "category `{}` has only {} sync token — limited recovery options",
                    rwfst.category(),
                    count,
                ),
                hint: Some(hint),
                grammar_name: Some(ctx.grammar_name.to_string()),
                source_location: None,
            });
        }
    }
}

/// Assess sync token quality via decision tree depth.
fn assess_sync_quality(
    ctx: &LintContext,
    rwfst: &crate::recovery::RecoveryWfst,
) -> String {
    let tree = match ctx.decision_trees.get(rwfst.category()) {
        Some(t) => t,
        None => return String::new(),
    };

    let mut quality_parts = Vec::new();
    for &token_id in rwfst.sync_tokens() {
        let token_name = match rwfst.token_name(token_id) {
            Some(n) => n.to_string(),
            None => continue,
        };
        let strategy = tree.dispatch_strategy(&token_name, ctx.token_id_map);
        let quality = match &strategy {
            crate::decision_tree::DispatchStrategy::Singleton { .. } => "excellent (depth 0)",
            crate::decision_tree::DispatchStrategy::DisjointSuffix { shared_prefix_len, .. } => {
                if *shared_prefix_len <= 1 { "good (shallow)" } else { "fair (deep prefix)" }
            }
            crate::decision_tree::DispatchStrategy::NfaTryAll { shared_prefix_len, .. } => {
                if *shared_prefix_len == 0 { "fair (ambiguous at root)" } else { "poor (deep + ambiguous)" }
            }
            crate::decision_tree::DispatchStrategy::NotPresent => "N/A (not in trie)",
        };
        quality_parts.push(format!("`{}`: {}", token_name, quality));
    }
    if quality_parts.is_empty() {
        String::new()
    } else {
        format!("Sync token quality: {}", quality_parts.join(", "))
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// R05: Missing Bracket Sync
// ══════════════════════════════════════════════════════════════════════════════

fn lint_r05_missing_bracket_sync(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let bracket_pairs = [("(", "RParen"), ("{", "RBrace"), ("[", "RBracket")];

    let category_names: Vec<String> = ctx.categories.iter().map(|c| c.name.clone()).collect();

    for cat in &category_names {
        // Collect terminals used by rules in this category
        let mut cat_terminals: HashSet<String> = HashSet::new();
        for (_, category, syntax) in ctx.all_syntax {
            if category == cat {
                for t in collect_terminals_flat(syntax) {
                    cat_terminals.insert(t);
                }
            }
        }

        // Find the recovery WFST for this category
        let rwfst = match ctx.recovery_wfsts.iter().find(|r| r.category() == cat) {
            Some(r) => r,
            None => continue,
        };

        for &(open, close_variant) in &bracket_pairs {
            if cat_terminals.contains(open) {
                // Check if closing bracket is in sync set
                // The sync set uses TokenIds — we need to check by variant name
                // The TokenIdMap resolves names. Check if the closing variant
                // appears in any sync token name.
                let has_close_sync = rwfst.sync_tokens().iter().any(|&id| {
                    rwfst
                        .token_name(id)
                        .map_or(false, |name| name == close_variant)
                });

                if !has_close_sync {
                    diagnostics.push(LintDiagnostic {
                        id: "R05",
                        name: "missing-bracket-sync",
                        severity: LintSeverity::Warning,
                        category: Some(cat.clone()),
                        rule: None,
                        message: format!(
                            "category `{}` uses `{}` delimiter but closing `{}` is \
                             absent from sync set",
                            cat, open, close_variant,
                        ),
                        hint: Some(
                            "ensure the closing bracket is in the category's FOLLOW set \
                             or structural delimiters"
                                .to_string(),
                        ),
                        grammar_name: Some(ctx.grammar_name.to_string()),
                        source_location: None,
                    });
                }
            }
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// R06: Inverted Recovery Costs
// ══════════════════════════════════════════════════════════════════════════════

fn lint_r06_inverted_recovery_costs(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let config = ctx.recovery_config;

    // Expected hierarchy: skip < delete < swap < substitute < insert
    let expected_order = [
        ("skip_per_token", config.skip_per_token),
        ("delete_cost", config.delete_cost),
        ("swap_cost", config.swap_cost),
        ("substitute_cost", config.substitute_cost),
        ("insert_cost", config.insert_cost),
    ];

    for i in 0..expected_order.len() {
        for j in (i + 1)..expected_order.len() {
            let (name_i, cost_i) = expected_order[i];
            let (name_j, cost_j) = expected_order[j];

            if cost_i > cost_j {
                diagnostics.push(LintDiagnostic {
                    id: "R06",
                    name: "inverted-recovery-costs",
                    severity: LintSeverity::Warning,
                    category: None,
                    rule: None,
                    message: format!(
                        "RecoveryConfig cost hierarchy violated: {} ({:.2}) > {} ({:.2})",
                        name_i, cost_i, name_j, cost_j,
                    ),
                    hint: Some(format!(
                        "expected hierarchy: skip < delete < swap < substitute < insert; \
                         adjust {} or {} to restore the hierarchy",
                        name_i, name_j,
                    )),
                    grammar_name: Some(ctx.grammar_name.to_string()),
                    source_location: None,
                });
            }
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// R07: Transposition Candidate
// ══════════════════════════════════════════════════════════════════════════════

fn lint_r07_transposition_candidate(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    // Collect all unique operator terminals from the grammar
    let mut all_operators: Vec<String> = Vec::new();
    for (_, _, syntax) in ctx.all_syntax {
        for item in syntax {
            if let SyntaxItemSpec::Terminal(t) = item {
                // Skip structural delimiters
                if !matches!(t.as_str(), "(" | ")" | "{" | "}" | "[" | "]" | "," | ";") {
                    all_operators.push(t.clone());
                }
            }
        }
    }
    all_operators.sort();
    all_operators.dedup();

    // Collect all pairs with Levenshtein distance = 1 into a single list
    let mut pairs: Vec<(String, String)> = Vec::new();
    for i in 0..all_operators.len() {
        for j in (i + 1)..all_operators.len() {
            let a = &all_operators[i];
            let b = &all_operators[j];
            if char_edit_distance_is_one(a, b) {
                pairs.push((a.clone(), b.clone()));
            }
        }
    }

    if pairs.is_empty() {
        return;
    }

    // Emit a single summary note instead of O(n²) individual notes
    let total = pairs.len();
    let max_samples = 8;
    let samples: Vec<String> = pairs
        .iter()
        .take(max_samples)
        .map(|(a, b)| format!("`{}`\u{2194}`{}`", a, b))
        .collect();

    let mut message = format!(
        "{} operator pair(s) differ by 1 character (SwapTokens repair candidates): {}",
        total,
        samples.join(", "),
    );
    if total > max_samples {
        message.push_str(&format!(" ({} more)", total - max_samples));
    }

    diagnostics.push(LintDiagnostic {
        id: "R07",
        name: "transposition-candidate",
        severity: LintSeverity::Note,
        category: None,
        rule: None,
        message,
        hint: Some(
            "the error recovery system can detect and fix common \
             typos between these operators via SwapTokens"
                .to_string(),
        ),
        grammar_name: Some(ctx.grammar_name.to_string()),
        source_location: None,
    });
}

/// Check if two strings have Levenshtein distance exactly 1.
fn char_edit_distance_is_one(a: &str, b: &str) -> bool {
    let a_chars: Vec<char> = a.chars().collect();
    let b_chars: Vec<char> = b.chars().collect();
    let len_a = a_chars.len();
    let len_b = b_chars.len();

    match (len_a as isize) - (len_b as isize) {
        0 => {
            // Same length: exactly one substitution
            let mut diffs = 0;
            for i in 0..len_a {
                if a_chars[i] != b_chars[i] {
                    diffs += 1;
                    if diffs > 1 {
                        return false;
                    }
                }
            }
            diffs == 1
        }
        1 => {
            // a is one longer: one insertion in a (= one deletion from a to get b)
            one_insertion_away(&a_chars, &b_chars)
        }
        -1 => {
            // b is one longer: one insertion in b
            one_insertion_away(&b_chars, &a_chars)
        }
        _ => false,
    }
}

/// Check if `longer` can become `shorter` by removing exactly one character.
fn one_insertion_away(longer: &[char], shorter: &[char]) -> bool {
    let mut i = 0;
    let mut j = 0;
    let mut skipped = false;
    while i < longer.len() && j < shorter.len() {
        if longer[i] != shorter[j] {
            if skipped {
                return false;
            }
            skipped = true;
            i += 1;
        } else {
            i += 1;
            j += 1;
        }
    }
    true
}

// ══════════════════════════════════════════════════════════════════════════════
// C01: Cast Cycle
// ══════════════════════════════════════════════════════════════════════════════

fn lint_c01_cast_cycle(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    // Build adjacency list from cast rules
    let mut adjacency: HashMap<&str, Vec<&str>> = HashMap::new();
    for cast in ctx.cast_rules {
        adjacency
            .entry(cast.source_category.as_str())
            .or_default()
            .push(cast.target_category.as_str());
    }

    // DFS with coloring: White (unvisited), Gray (in stack), Black (done)
    #[derive(Clone, Copy, PartialEq)]
    enum Color {
        White,
        Gray,
        Black,
    }

    let category_names: Vec<&str> = ctx.categories.iter().map(|c| c.name.as_str()).collect();
    let mut color: HashMap<&str, Color> = category_names
        .iter()
        .map(|&c| (c, Color::White))
        .collect();
    let mut path: Vec<&str> = Vec::new();

    fn dfs<'a>(
        node: &'a str,
        adjacency: &HashMap<&'a str, Vec<&'a str>>,
        color: &mut HashMap<&'a str, Color>,
        path: &mut Vec<&'a str>,
        diagnostics: &mut Vec<LintDiagnostic>,
        grammar_name: &str,
    ) {
        color.insert(node, Color::Gray);
        path.push(node);

        if let Some(neighbors) = adjacency.get(node) {
            for &next in neighbors {
                match color.get(next) {
                    Some(Color::Gray) => {
                        // Found a cycle — extract the cycle path
                        let cycle_start = path.iter().position(|&n| n == next).unwrap_or(0);
                        let mut cycle_path: Vec<&str> =
                            path[cycle_start..].to_vec();
                        cycle_path.push(next);
                        let cycle_str = cycle_path.join(" -> ");

                        diagnostics.push(LintDiagnostic {
                            id: "C01",
                            name: "cast-cycle",
                            severity: LintSeverity::Error,
                            category: None,
                            rule: None,
                            message: format!("cast cycle detected: {}", cycle_str),
                            hint: Some(
                                "break the cycle by removing one cast direction".to_string(),
                            ),
                            grammar_name: Some(grammar_name.to_string()),
                            source_location: None,
                        });
                    }
                    Some(Color::White) | None => {
                        dfs(next, adjacency, color, path, diagnostics, grammar_name);
                    }
                    Some(Color::Black) => {
                        // Already fully explored, no cycle through this node
                    }
                }
            }
        }

        path.pop();
        color.insert(node, Color::Black);
    }

    for &cat in &category_names {
        if color.get(cat) == Some(&Color::White) {
            dfs(cat, &adjacency, &mut color, &mut path, diagnostics, ctx.grammar_name);
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// C02: Transitive Cast Redundancy
// ══════════════════════════════════════════════════════════════════════════════

fn lint_c02_transitive_cast_redundancy(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    // Build adjacency list
    let mut adjacency: HashMap<&str, HashSet<&str>> = HashMap::new();
    for cast in ctx.cast_rules {
        adjacency
            .entry(cast.source_category.as_str())
            .or_default()
            .insert(cast.target_category.as_str());
    }

    let category_names: Vec<&str> = ctx.categories.iter().map(|c| c.name.as_str()).collect();

    // Compute transitive closure via Floyd-Warshall-style approach
    let mut reachable: HashMap<(&str, &str), bool> = HashMap::new();
    for &src in &category_names {
        for &dst in &category_names {
            reachable.insert(
                (src, dst),
                adjacency
                    .get(src)
                    .map_or(false, |neighbors| neighbors.contains(dst)),
            );
        }
    }

    for &mid in &category_names {
        for &src in &category_names {
            for &dst in &category_names {
                if reachable[&(src, mid)] && reachable[&(mid, dst)] {
                    reachable.insert((src, dst), true);
                }
            }
        }
    }

    // Check for direct cast A→C alongside transitive A→...→C (path length ≥ 2)
    for cast in ctx.cast_rules {
        let src = cast.source_category.as_str();
        let dst = cast.target_category.as_str();

        // Is there a path of length ≥ 2 from src to dst?
        let has_indirect = adjacency.get(src).map_or(false, |neighbors| {
            neighbors.iter().any(|&mid| {
                mid != dst
                    && reachable
                        .get(&(mid, dst))
                        .copied()
                        .unwrap_or(false)
            })
        });

        if has_indirect {
            diagnostics.push(LintDiagnostic {
                id: "C02",
                name: "transitive-cast-redundancy",
                severity: LintSeverity::Note,
                category: None,
                rule: Some(cast.label.clone()),
                message: format!(
                    "direct cast `{}` → `{}` (rule `{}`) is redundant — a transitive \
                     path already exists",
                    src, dst, cast.label,
                ),
                hint: Some(
                    "the transitive path handles this cast — the direct rule may be \
                     intentional for performance or explicitness"
                        .to_string(),
                ),
                grammar_name: Some(ctx.grammar_name.to_string()),
                source_location: None,
            });
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// C04: Wide Cross Overlap
// ══════════════════════════════════════════════════════════════════════════════

fn lint_c04_wide_cross_overlap(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let category_names: Vec<String> = ctx.categories.iter().map(|c| c.name.clone()).collect();

    for i in 0..category_names.len() {
        for j in (i + 1)..category_names.len() {
            let cat_a = &category_names[i];
            let cat_b = &category_names[j];

            let first_a = match ctx.first_sets.get(cat_a) {
                Some(fs) => fs,
                None => continue,
            };
            let first_b = match ctx.first_sets.get(cat_b) {
                Some(fs) => fs,
                None => continue,
            };

            let overlap = first_a.intersection(first_b);
            let overlap_count = overlap.tokens.len();

            if first_a.tokens.is_empty() || first_b.tokens.is_empty() {
                continue;
            }

            // Check overlap relative to the smaller FIRST set
            let min_size = first_a.tokens.len().min(first_b.tokens.len());
            let ratio = overlap_count as f64 / min_size as f64;

            if ratio >= 0.8 && overlap_count >= 2 {
                // Build token-level breakdown using decision trees
                let mut token_breakdown: Vec<String> = Vec::new();
                for token in overlap.sorted_tokens() {
                    let rules_a = tree_rules_for_token(ctx, cat_a, &token);
                    let rules_b = tree_rules_for_token(ctx, cat_b, &token);
                    if !rules_a.is_empty() || !rules_b.is_empty() {
                        token_breakdown.push(format!(
                            "`{}` ({}:{} vs {}:{})",
                            token,
                            cat_a,
                            if rules_a.is_empty() { "cast".to_string() } else { rules_a.join("/") },
                            cat_b,
                            if rules_b.is_empty() { "cast".to_string() } else { rules_b.join("/") },
                        ));
                    }
                }

                let message = if token_breakdown.is_empty() {
                    format!(
                        "cross-category overlap between `{}` and `{}`: {}/{} tokens ({:.0}%) \
                         — mostly save/restore dispatch",
                        cat_a, cat_b, overlap_count, min_size, ratio * 100.0,
                    )
                } else {
                    format!(
                        "cross-category overlap between `{}` and `{}`: {}/{} tokens ({:.0}%): [{}]",
                        cat_a, cat_b, overlap_count, min_size, ratio * 100.0,
                        token_breakdown.join(", "),
                    )
                };

                diagnostics.push(LintDiagnostic {
                    id: "C04",
                    name: "wide-cross-overlap",
                    severity: LintSeverity::Note,
                    category: None,
                    rule: None,
                    message,
                    hint: Some(
                        "high FIRST-set overlap means many tokens need save/restore \
                         backtracking in cross-category dispatch"
                            .to_string(),
                    ),
                    grammar_name: Some(ctx.grammar_name.to_string()),
                    source_location: None,
                });
            }
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// P02: High NFA Spillover
// ══════════════════════════════════════════════════════════════════════════════

fn lint_p02_high_nfa_spillover(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    if ctx.nfa_spillover_categories.len() > 3 {
        let mut sorted_cats: Vec<&String> = ctx.nfa_spillover_categories.iter().collect();
        sorted_cats.sort();
        let cats_str: Vec<&str> = sorted_cats.iter().map(|s| s.as_str()).collect();
        // Modulate severity: tiny grammars (<10 categories) → Note, larger → Warning
        let severity = if ctx.grammar_profile
            .map_or(false, |p| p.category_count >= 10) {
            LintSeverity::Warning
        } else {
            LintSeverity::Note
        };
        diagnostics.push(LintDiagnostic {
            id: "P02",
            name: "high-nfa-spillover",
            severity,
            category: None,
            rule: None,
            message: format!(
                "{} categories need NFA spillover buffers: [{}] — increases TLS overhead",
                ctx.nfa_spillover_categories.len(),
                cats_str.join(", "),
            ),
            hint: Some(
                "reduce prefix ambiguity to lower the number of categories needing \
                 NFA spillover"
                    .to_string(),
            ),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// P03: Deep Cast Nesting
// ══════════════════════════════════════════════════════════════════════════════

fn lint_p03_deep_cast_nesting(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    // Build cast DAG adjacency list
    let mut adjacency: HashMap<&str, Vec<&str>> = HashMap::new();
    for cast in ctx.cast_rules {
        adjacency
            .entry(cast.source_category.as_str())
            .or_default()
            .push(cast.target_category.as_str());
    }

    let category_names: Vec<&str> = ctx.categories.iter().map(|c| c.name.as_str()).collect();

    // Topological sort + DP to find longest path (only valid for DAGs — C01 catches cycles)
    let mut longest_path: HashMap<&str, usize> = HashMap::new();

    fn dp_longest<'a>(
        node: &'a str,
        adjacency: &HashMap<&'a str, Vec<&'a str>>,
        memo: &mut HashMap<&'a str, usize>,
        visited: &mut HashSet<&'a str>,
    ) -> usize {
        if let Some(&cached) = memo.get(node) {
            return cached;
        }
        // Cycle guard (C01 should catch this, but be defensive)
        if !visited.insert(node) {
            return 0;
        }

        let max_child = adjacency
            .get(node)
            .map_or(0, |neighbors| {
                neighbors
                    .iter()
                    .map(|&next| dp_longest(next, adjacency, memo, visited) + 1)
                    .max()
                    .unwrap_or(0)
            });

        visited.remove(node);
        memo.insert(node, max_child);
        max_child
    }

    let mut visited = HashSet::new();
    for &cat in &category_names {
        dp_longest(cat, &adjacency, &mut longest_path, &mut visited);
    }

    let max_depth = longest_path.values().copied().max().unwrap_or(0);
    if max_depth > 3 {
        let deepest = longest_path
            .iter()
            .filter(|(_, &d)| d == max_depth)
            .map(|(&name, _)| name)
            .collect::<Vec<_>>();

        // Modulate severity: tiny grammars (<10 categories) → Note, larger → Warning
        let severity = if ctx.grammar_profile
            .map_or(false, |p| p.category_count >= 10) {
            LintSeverity::Warning
        } else {
            LintSeverity::Note
        };
        diagnostics.push(LintDiagnostic {
            id: "P03",
            name: "deep-cast-nesting",
            severity,
            category: None,
            rule: None,
            message: format!(
                "cast chain depth is {} (starting from [{}]) — each level adds \
                 Box::new() wrapper overhead",
                max_depth,
                deepest.join(", "),
            ),
            hint: Some(
                "consider adding direct cast rules to bypass intermediate categories"
                    .to_string(),
            ),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// P04: Many Alternatives
// ══════════════════════════════════════════════════════════════════════════════

fn lint_p04_many_alternatives(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let category_names: Vec<String> = ctx.categories.iter().map(|c| c.name.clone()).collect();

    for cat in &category_names {
        if let Some(wfst) = ctx.prediction_wfsts.get(cat.as_str()) {
            if let Some(first_set) = ctx.first_sets.get(cat) {
                for token in first_set.sorted_tokens() {
                    let actions = wfst.predict(&token);
                    if actions.len() > 4 {
                        // Modulate severity: tiny grammars (<10 categories) → Note, larger → Warning
                        let severity = if ctx.grammar_profile
                            .map_or(false, |p| p.category_count >= 10) {
                            LintSeverity::Warning
                        } else {
                            LintSeverity::Note
                        };
                        diagnostics.push(LintDiagnostic {
                            id: "P04",
                            name: "many-alternatives",
                            severity,
                            category: Some(cat.clone()),
                            rule: None,
                            message: format!(
                                "token `{}` dispatches to {} rules in category `{}` — \
                                 save/restore overhead",
                                token,
                                actions.len(),
                                cat,
                            ),
                            hint: Some(
                                "reduce prefix ambiguity or use beam pruning to limit \
                                 alternatives"
                                    .to_string(),
                            ),
                            grammar_name: Some(ctx.grammar_name.to_string()),
                            source_location: None,
                        });
                    }
                }
            }
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Composition-specific lints (X01–X05)
// ══════════════════════════════════════════════════════════════════════════════

/// Pre/post composition data needed for composition-specific lints.
///
/// Captures the FIRST sets, prediction WFSTs, dead rules, and terminal semantics
/// for two grammars (A and B) before and after composition (merged). The
/// `shared_categories` field lists categories that exist in both source grammars.
pub struct CompositionLintContext<'a> {
    /// FIRST sets from grammar A (before merge).
    pub first_sets_a: &'a HashMap<String, FirstSet>,
    /// FIRST sets from grammar B (before merge).
    pub first_sets_b: &'a HashMap<String, FirstSet>,
    /// FIRST sets from the merged grammar.
    pub first_sets_merged: &'a HashMap<String, FirstSet>,
    /// Prediction WFSTs from grammar A.
    pub prediction_wfsts_a: &'a HashMap<String, PredictionWfst>,
    /// Prediction WFSTs from grammar B.
    pub prediction_wfsts_b: &'a HashMap<String, PredictionWfst>,
    /// Categories present in both grammars.
    pub shared_categories: &'a [String],
    /// Dead rules in grammar A (rule labels).
    pub dead_rules_a: &'a HashSet<String>,
    /// Dead rules in grammar B (rule labels).
    pub dead_rules_b: &'a HashSet<String>,
    /// Dead rules in the merged grammar (rule labels).
    pub dead_rules_merged: &'a HashSet<String>,
    /// Rules from grammar A.
    pub rules_a: &'a [RuleInfo],
    /// Rules from grammar B.
    pub rules_b: &'a [RuleInfo],
    /// Terminal semantics in grammar A: terminal name -> [(category, semantic role)].
    pub terminal_semantics_a: &'a HashMap<String, Vec<(String, String)>>,
    /// Terminal semantics in grammar B: terminal name -> [(category, semantic role)].
    pub terminal_semantics_b: &'a HashMap<String, Vec<(String, String)>>,
}

/// Run all composition-specific lints and return structured diagnostics.
///
/// These lints detect issues that arise when two grammars are composed
/// (merged). They compare the pre-composition state of each source grammar
/// against the merged result to detect ambiguity introduction, priority
/// shadowing, newly-dead rules, broken cast chains, and terminal collisions.
pub fn run_composition_lints(
    base_ctx: &LintContext,
    comp_ctx: &CompositionLintContext,
) -> Vec<LintDiagnostic> {
    let mut diagnostics = Vec::new();

    lint_x01_composition_ambiguity_introduction(base_ctx, comp_ctx, &mut diagnostics);
    lint_x02_composition_priority_shadowing(base_ctx, comp_ctx, &mut diagnostics);
    lint_x03_composition_dead_rule_creation(base_ctx, comp_ctx, &mut diagnostics);
    lint_x04_composition_cast_chain_break(base_ctx, comp_ctx, &mut diagnostics);
    lint_x05_composition_terminal_collision(base_ctx, comp_ctx, &mut diagnostics);

    diagnostics
}

// ──────────────────────────────────────────────────────────────────────────────
// X01: Composition Ambiguity Introduction
// ──────────────────────────────────────────────────────────────────────────────

/// Detects FIRST set ambiguity growth after merge for shared categories.
///
/// Two sources of composition-introduced ambiguity are detected:
///
/// 1. **New FIRST set overlap:** Tokens that appear in the merged FIRST set
///    but not in the union of A's and B's FIRST sets. These represent new
///    derivation paths created by composition (e.g., through cross-category
///    casts that only exist in the merged grammar).
///
/// 2. **Pre-existing overlap amplification:** The FIRST set overlap between
///    A and B (tokens in both) is checked against the merged FIRST set. If
///    the merged set contains the same overlapping tokens plus additional
///    tokens from new derivation paths, the ambiguity has grown.
fn lint_x01_composition_ambiguity_introduction(
    base_ctx: &LintContext,
    comp_ctx: &CompositionLintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    for cat in comp_ctx.shared_categories {
        let first_a = match comp_ctx.first_sets_a.get(cat) {
            Some(fs) => fs,
            None => continue,
        };
        let first_b = match comp_ctx.first_sets_b.get(cat) {
            Some(fs) => fs,
            None => continue,
        };
        let first_merged = match comp_ctx.first_sets_merged.get(cat) {
            Some(fs) => fs,
            None => continue,
        };

        // Pre-composition overlap: tokens in BOTH A and B for this category.
        let pre_overlap = first_a.intersection(first_b);

        // Union of A's and B's FIRST sets.
        let mut pre_union = first_a.clone();
        pre_union.union(first_b);

        // Tokens in the merged FIRST set that are NOT in the pre-composition
        // union represent new derivation paths introduced by the composition.
        let new_tokens: Vec<&str> = first_merged.tokens.iter()
            .filter(|t| !pre_union.contains(t))
            .map(|s| s.as_str())
            .collect();

        // Also check: did the pre-existing overlap (tokens in both A and B)
        // grow in the merged result? This can happen when composition adds
        // new nonterminal edges that make previously non-overlapping tokens
        // now reachable from both source grammars.
        //
        // Merged overlap = tokens in merged that appear in BOTH the original
        // A first set AND the original B first set. Since A and B are fixed
        // source sets, this is bounded by |A ∩ B|. However, the merged set
        // may also have tokens that create NEW overlap between different
        // rules within the composed grammar. We detect this via new_tokens.

        let pre_overlap_count = pre_overlap.tokens.len();

        if !new_tokens.is_empty() {
            let mut sorted_new = new_tokens;
            sorted_new.sort_unstable();

            diagnostics.push(LintDiagnostic {
                id: "X01",
                name: "composition-ambiguity-introduction",
                severity: LintSeverity::Warning,
                category: Some(cat.clone()),
                rule: None,
                message: format!(
                    "composition introduces {} new FIRST set token(s) in category `{}` \
                     not in either source grammar: [{}] \
                     (pre-composition overlap: {} token(s))",
                    sorted_new.len(), cat, sorted_new.join(", "), pre_overlap_count,
                ),
                hint: Some(
                    "add unique prefix tokens to disambiguate, or use WFST weights \
                     to express priority between the composed grammars"
                        .to_string(),
                ),
                grammar_name: Some(base_ctx.grammar_name.to_string()),
                source_location: None,
            });
        }
    }
}

// ──────────────────────────────────────────────────────────────────────────────
// X02: Composition Priority Shadowing
// ──────────────────────────────────────────────────────────────────────────────

/// Detects when a rule from grammar A is shadowed (has lower priority) by a
/// rule from grammar B for the same token in a shared category.
///
/// For each shared category, queries the prediction WFSTs from A and B for
/// each token in the merged FIRST set. If both A and B have predictions for
/// the same token and A's best weight is strictly greater (worse) than B's
/// best weight, A's rule is shadowed by B's.
fn lint_x02_composition_priority_shadowing(
    base_ctx: &LintContext,
    comp_ctx: &CompositionLintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    for cat in comp_ctx.shared_categories {
        let wfst_a = match comp_ctx.prediction_wfsts_a.get(cat) {
            Some(w) => w,
            None => continue,
        };
        let wfst_b = match comp_ctx.prediction_wfsts_b.get(cat) {
            Some(w) => w,
            None => continue,
        };

        // Collect all tokens from both FIRST sets for this category
        let mut all_tokens: HashSet<&str> = HashSet::new();
        if let Some(fs_a) = comp_ctx.first_sets_a.get(cat) {
            all_tokens.extend(fs_a.tokens.iter().map(|s| s.as_str()));
        }
        if let Some(fs_b) = comp_ctx.first_sets_b.get(cat) {
            all_tokens.extend(fs_b.tokens.iter().map(|s| s.as_str()));
        }

        let mut sorted_tokens: Vec<&str> = all_tokens.into_iter().collect();
        sorted_tokens.sort_unstable();

        for token in sorted_tokens {
            let actions_a = wfst_a.predict(token);
            let actions_b = wfst_b.predict(token);

            if let (Some(best_a), Some(best_b)) = (actions_a.first(), actions_b.first()) {
                // A is shadowed by B: A's best weight is strictly worse (higher)
                if best_a.weight > best_b.weight {
                    diagnostics.push(LintDiagnostic {
                        id: "X02",
                        name: "composition-priority-shadowing",
                        severity: LintSeverity::Warning,
                        category: Some(cat.clone()),
                        rule: Some(best_a.action.rule_label()),
                        message: format!(
                            "rule `{}` from grammar A is shadowed by `{}` from grammar B \
                             for token `{}` in category `{}` \
                             (weight {:.3} vs {:.3})",
                            best_a.action.rule_label(),
                            best_b.action.rule_label(),
                            token,
                            cat,
                            best_a.weight.value(),
                            best_b.weight.value(),
                        ),
                        hint: Some(
                            "adjust WFST weights or rename rules to avoid unintended \
                             priority override"
                                .to_string(),
                        ),
                        grammar_name: Some(base_ctx.grammar_name.to_string()),
                        source_location: None,
                    });
                }
            }
        }
    }
}

// ──────────────────────────────────────────────────────────────────────────────
// X03: Composition Dead Rule Creation
// ──────────────────────────────────────────────────────────────────────────────

/// Detects rules that were live in their source grammar but became dead
/// after composition.
///
/// Computes `dead_rules_merged \ (dead_rules_a ∪ dead_rules_b)` — rules that
/// are dead in the merged grammar but were NOT dead in either source. These
/// represent rules that the merge rendered unreachable.
fn lint_x03_composition_dead_rule_creation(
    base_ctx: &LintContext,
    comp_ctx: &CompositionLintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    // Rules dead in merged but not dead in either source
    let pre_dead: HashSet<&String> = comp_ctx
        .dead_rules_a
        .iter()
        .chain(comp_ctx.dead_rules_b.iter())
        .collect();

    let mut newly_dead: Vec<&String> = comp_ctx
        .dead_rules_merged
        .iter()
        .filter(|r| !pre_dead.contains(r))
        .collect();

    // Sort for deterministic output
    newly_dead.sort();

    for rule_label in newly_dead {
        // Determine which source grammar the rule came from
        let source_grammar = if comp_ctx.rules_a.iter().any(|r| r.label == *rule_label) {
            "A"
        } else if comp_ctx.rules_b.iter().any(|r| r.label == *rule_label) {
            "B"
        } else {
            "unknown"
        };

        // Find the category for this rule
        let category = comp_ctx
            .rules_a
            .iter()
            .chain(comp_ctx.rules_b.iter())
            .find(|r| r.label == *rule_label)
            .map(|r| r.category.clone());

        diagnostics.push(LintDiagnostic {
            id: "X03",
            name: "composition-dead-rule-creation",
            severity: LintSeverity::Warning,
            category: category.clone(),
            rule: Some(rule_label.clone()),
            message: format!(
                "rule `{}` was live in grammar {} but became dead after composition{}",
                rule_label,
                source_grammar,
                category
                    .as_ref()
                    .map(|c| format!(" (category `{}`)", c))
                    .unwrap_or_default(),
            ),
            hint: Some(
                "the composed grammar may have a higher-priority rule that shadows \
                 this one — verify intent or adjust weights"
                    .to_string(),
            ),
            grammar_name: Some(base_ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

// ──────────────────────────────────────────────────────────────────────────────
// X04: Composition Cast Chain Break
// ──────────────────────────────────────────────────────────────────────────────

/// Detects cast chains that exist in a source grammar but are broken after
/// composition.
///
/// A cast chain is a path A -> B -> C -> ... in the cast rule graph. If
/// merging removes or overrides an intermediate cast, the chain breaks.
/// This lint checks that all cast chains present in base_ctx.cast_rules
/// can still be traversed in the merged grammar (using the same cast_rules
/// in base_ctx, which represents the merged state).
///
/// The check verifies that for every pair of categories (src, dst) reachable
/// via cast chains in either source grammar, the same reachability holds in
/// the merged cast graph.
fn lint_x04_composition_cast_chain_break(
    base_ctx: &LintContext,
    comp_ctx: &CompositionLintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    /// Compute reachability closure from a set of cast rules.
    fn reachability(cast_rules: &[CastRule]) -> HashSet<(String, String)> {
        // Build adjacency list
        let mut adjacency: HashMap<&str, HashSet<&str>> = HashMap::new();
        for cast in cast_rules {
            adjacency
                .entry(cast.source_category.as_str())
                .or_default()
                .insert(cast.target_category.as_str());
        }

        // Collect all categories
        let mut cats: HashSet<&str> = HashSet::new();
        for cast in cast_rules {
            cats.insert(cast.source_category.as_str());
            cats.insert(cast.target_category.as_str());
        }

        // Compute transitive closure via repeated BFS from each node
        let mut reachable = HashSet::new();
        for &src in &cats {
            let mut visited = HashSet::new();
            let mut queue = Vec::new();
            if let Some(neighbors) = adjacency.get(src) {
                queue.extend(neighbors.iter().copied());
            }
            while let Some(node) = queue.pop() {
                if visited.insert(node) {
                    reachable.insert((src.to_string(), node.to_string()));
                    if let Some(neighbors) = adjacency.get(node) {
                        for &next in neighbors {
                            if !visited.contains(next) {
                                queue.push(next);
                            }
                        }
                    }
                }
            }
        }
        reachable
    }

    // Build cast rules for each source grammar from their rule info
    // Source A casts: rules in A that are casts
    let casts_a: Vec<CastRule> = comp_ctx
        .rules_a
        .iter()
        .filter(|r| r.is_cast)
        .filter_map(|r| {
            // Cast rules have a NonTerminal first item pointing to the source category
            r.first_items.iter().find_map(|item| {
                if let crate::prediction::FirstItem::NonTerminal(ref source_cat) = item {
                    Some(CastRule {
                        label: r.label.clone(),
                        source_category: source_cat.clone(),
                        target_category: r.category.clone(),
                    })
                } else {
                    None
                }
            })
        })
        .collect();

    let casts_b: Vec<CastRule> = comp_ctx
        .rules_b
        .iter()
        .filter(|r| r.is_cast)
        .filter_map(|r| {
            r.first_items.iter().find_map(|item| {
                if let crate::prediction::FirstItem::NonTerminal(ref source_cat) = item {
                    Some(CastRule {
                        label: r.label.clone(),
                        source_category: source_cat.clone(),
                        target_category: r.category.clone(),
                    })
                } else {
                    None
                }
            })
        })
        .collect();

    let reachable_a = reachability(&casts_a);
    let reachable_b = reachability(&casts_b);
    let reachable_merged = reachability(base_ctx.cast_rules);

    // Any pair reachable in source A or B but not in merged = broken chain
    let source_reachable: HashSet<(String, String)> = reachable_a
        .union(&reachable_b)
        .cloned()
        .collect();

    let mut broken_chains: Vec<(String, String)> = source_reachable
        .iter()
        .filter(|pair| !reachable_merged.contains(pair))
        .cloned()
        .collect();

    // Sort for deterministic output
    broken_chains.sort();

    for (src, dst) in broken_chains {
        let source_grammar = if reachable_a.contains(&(src.clone(), dst.clone())) {
            "A"
        } else {
            "B"
        };

        diagnostics.push(LintDiagnostic {
            id: "X04",
            name: "composition-cast-chain-break",
            severity: LintSeverity::Error,
            category: Some(dst.clone()),
            rule: None,
            message: format!(
                "cast chain `{}` -> `{}` from grammar {} is broken after composition",
                src, dst, source_grammar,
            ),
            hint: Some(
                "ensure all intermediate cast rules are preserved in the composed \
                 grammar, or add explicit casts to restore the chain"
                    .to_string(),
            ),
            grammar_name: Some(base_ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

// ──────────────────────────────────────────────────────────────────────────────
// X05: Composition Terminal Collision
// ──────────────────────────────────────────────────────────────────────────────

/// Detects when the same terminal string is used in different categories with
/// different semantic roles across the two source grammars.
///
/// For example, if grammar A uses `+` as an infix operator in category `Int`
/// (role: "infix") and grammar B uses `+` as a prefix operator in category
/// `Str` (role: "prefix"), this is a terminal collision that may cause
/// confusion or dispatch errors in the composed grammar.
fn lint_x05_composition_terminal_collision(
    base_ctx: &LintContext,
    comp_ctx: &CompositionLintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    // Find terminals that appear in both grammars
    let terminals_a: HashSet<&str> = comp_ctx
        .terminal_semantics_a
        .keys()
        .map(|s| s.as_str())
        .collect();
    let terminals_b: HashSet<&str> = comp_ctx
        .terminal_semantics_b
        .keys()
        .map(|s| s.as_str())
        .collect();

    let mut shared_terminals: Vec<&str> = terminals_a
        .intersection(&terminals_b)
        .copied()
        .collect();
    shared_terminals.sort_unstable();

    for terminal in shared_terminals {
        let semantics_a = &comp_ctx.terminal_semantics_a[terminal];
        let semantics_b = &comp_ctx.terminal_semantics_b[terminal];

        // Collect all roles from A and B
        let roles_a: HashSet<&str> = semantics_a.iter().map(|(_, role)| role.as_str()).collect();
        let roles_b: HashSet<&str> = semantics_b.iter().map(|(_, role)| role.as_str()).collect();

        // Check if any role in B is not present in A (i.e., different semantic use)
        let diff_in_b: Vec<&str> = roles_b.difference(&roles_a).copied().collect();
        let diff_in_a: Vec<&str> = roles_a.difference(&roles_b).copied().collect();

        if !diff_in_a.is_empty() || !diff_in_b.is_empty() {
            let mut all_roles: Vec<&str> = roles_a.union(&roles_b).copied().collect();
            all_roles.sort_unstable();

            // Collect categories from both for context
            let cats_a: Vec<&str> = semantics_a.iter().map(|(cat, _)| cat.as_str()).collect();
            let cats_b: Vec<&str> = semantics_b.iter().map(|(cat, _)| cat.as_str()).collect();

            diagnostics.push(LintDiagnostic {
                id: "X05",
                name: "composition-terminal-collision",
                severity: LintSeverity::Warning,
                category: None,
                rule: None,
                message: format!(
                    "terminal `{}` has different semantic roles across grammars: \
                     A uses it as [{}] in [{}], B uses it as [{}] in [{}]",
                    terminal,
                    roles_a.iter().copied().collect::<Vec<_>>().join(", "),
                    cats_a.join(", "),
                    roles_b.iter().copied().collect::<Vec<_>>().join(", "),
                    cats_b.join(", "),
                ),
                hint: Some(
                    "consider renaming the terminal in one grammar to avoid \
                     semantic confusion in the composed grammar"
                        .to_string(),
                ),
                grammar_name: Some(base_ctx.grammar_name.to_string()),
                source_location: None,
            });
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// W03+: Cross-Category Ambiguity Hotspot Ranking
// ══════════════════════════════════════════════════════════════════════════════

/// After per-category W03 emissions, aggregate ambiguity counts across ALL
/// categories per token. Rank tokens by total ambiguity impact.
fn lint_w03_cross_category_hotspot(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    if ctx.decision_trees.is_empty() {
        return;
    }

    // Accumulate per-token ambiguity counts across categories
    let mut token_ambiguity: HashMap<String, Vec<(String, usize)>> = HashMap::new();

    for (cat_name, tree) in ctx.decision_trees {
        let dispatch_tokens = tree.dispatch_tokens(ctx.token_id_map);
        for token_variant in &dispatch_tokens {
            let strategy = tree.dispatch_strategy(token_variant, ctx.token_id_map);
            let count = match &strategy {
                crate::decision_tree::DispatchStrategy::NfaTryAll { rule_labels, .. } => {
                    rule_labels.len()
                }
                _ => 0,
            };
            if count >= 2 {
                token_ambiguity
                    .entry(token_variant.clone())
                    .or_default()
                    .push((cat_name.clone(), count));
            }
        }
    }

    // Only report tokens ambiguous in 2+ categories
    let mut hotspots: Vec<(String, usize, Vec<(String, usize)>)> = token_ambiguity
        .into_iter()
        .filter(|(_, cats)| cats.len() >= 2)
        .map(|(token, cats)| {
            let total: usize = cats.iter().map(|(_, c)| *c).sum();
            (token, total, cats)
        })
        .collect();
    hotspots.sort_by(|a, b| b.1.cmp(&a.1));

    for (rank, (token, total, cats)) in hotspots.iter().enumerate() {
        let breakdown: Vec<String> = cats
            .iter()
            .map(|(cat, count)| format!("{}: {}", cat, count))
            .collect();
        diagnostics.push(LintDiagnostic {
            id: "W03",
            name: "cross-category-hotspot",
            severity: LintSeverity::Note,
            category: None,
            rule: None,
            message: format!(
                "token `{}` is #{} ambiguity hotspot: {} ambiguities across {} categories ({})",
                token,
                rank + 1,
                total,
                cats.len(),
                breakdown.join(", "),
            ),
            hint: Some(
                "consider left-factoring rules starting with this token to reduce cross-category ambiguity"
                    .to_string(),
            ),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// G32: Prefix Structural Isomorphism
// ══════════════════════════════════════════════════════════════════════════════

/// Detect categories with structurally identical dispatch tries.
/// Uses content hashing of the trie structure for comparison.
fn lint_g32_prefix_isomorphism(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    if ctx.decision_trees.len() < 2 {
        return;
    }

    // Hash each category's trie structure by serializing stats + dispatch tokens + strategies
    let mut hash_to_cats: HashMap<u64, Vec<String>> = HashMap::new();

    for (cat_name, tree) in ctx.decision_trees {
        use std::hash::{Hash, Hasher};
        use std::collections::hash_map::DefaultHasher;
        let mut hasher = DefaultHasher::new();

        // Hash the trie structure via all (path, action) pairs
        let mut entries: Vec<(Vec<u8>, String)> = tree.segments.iter()
            .flat_map(|seg| seg.iter())
            .map(|(path, action)| {
                let action_str = match action {
                    crate::decision_tree::DecisionAction::Commit { rule_label, .. } => {
                        format!("C:{}", rule_label)
                    }
                    crate::decision_tree::DecisionAction::Ambiguous { candidates } => {
                        let mut labels: Vec<&str> = candidates.iter()
                            .map(|c| c.rule_label.as_str())
                            .collect();
                        labels.sort();
                        format!("A:{}", labels.join(","))
                    }
                    crate::decision_tree::DecisionAction::NonterminalBoundary { options } => {
                        format!("NT:{}", options.len())
                    }
                };
                (path, action_str)
            })
            .collect();
        entries.sort();

        // Hash the sorted entries (structure, not content) — compare shapes, not labels
        entries.len().hash(&mut hasher);
        for (path, _) in &entries {
            path.hash(&mut hasher);
        }
        tree.stats.total_states.hash(&mut hasher);
        tree.stats.ambiguous_nodes.hash(&mut hasher);
        tree.stats.max_depth.hash(&mut hasher);

        let hash = hasher.finish();
        hash_to_cats.entry(hash).or_default().push(cat_name.clone());
    }

    for cats in hash_to_cats.values() {
        if cats.len() >= 2 {
            let mut sorted = cats.clone();
            sorted.sort();
            diagnostics.push(LintDiagnostic {
                id: "G32",
                name: "prefix-isomorphism",
                severity: LintSeverity::Note,
                category: None,
                rule: None,
                message: format!(
                    "categories [{}] have structurally identical dispatch tries; \
                     they could share parser code via parameterization",
                    sorted.join(", "),
                ),
                hint: Some(
                    "consider using a generic parser parameterized over the category type"
                        .to_string(),
                ),
                grammar_name: Some(ctx.grammar_name.to_string()),
                source_location: None,
            });
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// D10: Lookahead Waste
// ══════════════════════════════════════════════════════════════════════════════

/// Detect when generated lookahead is deeper than necessary.
/// Compares TreeStats.max_depth vs per-token resolution depth.
fn lint_d10_lookahead_waste(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    for (cat_name, tree) in ctx.decision_trees {
        if tree.stats.total_states == 0 || tree.stats.max_depth <= 1 {
            continue;
        }

        let dispatch_tokens = tree.dispatch_tokens(ctx.token_id_map);
        let mut depth1_count = 0usize;
        let mut total_tokens = 0usize;

        for token_variant in &dispatch_tokens {
            total_tokens += 1;
            let strategy = tree.dispatch_strategy(token_variant, ctx.token_id_map);
            match &strategy {
                crate::decision_tree::DispatchStrategy::Singleton { .. } => {
                    depth1_count += 1;
                }
                crate::decision_tree::DispatchStrategy::DisjointSuffix { shared_prefix_len, .. } => {
                    if *shared_prefix_len == 0 {
                        depth1_count += 1;
                    }
                }
                _ => {}
            }
        }

        if total_tokens > 0 && tree.stats.max_depth > 2 {
            let depth1_pct = depth1_count as f64 / total_tokens as f64 * 100.0;
            if depth1_pct >= 80.0 {
                diagnostics.push(LintDiagnostic {
                    id: "D10",
                    name: "lookahead-waste",
                    severity: LintSeverity::Note,
                    category: Some(cat_name.clone()),
                    rule: None,
                    message: format!(
                        "category `{}`: {}-token max lookahead generated but 1-token suffices \
                         for {:.0}% ({}/{}) of dispatch points",
                        cat_name,
                        tree.stats.max_depth,
                        depth1_pct,
                        depth1_count,
                        total_tokens,
                    ),
                    hint: Some(
                        "the few deep-lookahead tokens may be candidates for left-factoring"
                            .to_string(),
                    ),
                    grammar_name: Some(ctx.grammar_name.to_string()),
                    source_location: None,
                });
            }
        }
    }
}

/// 2e: Ascent equation x dispatch trie correlation.
///
/// Detects parsed-but-never-rewritten constructors: rules reachable in the
/// trie (they can be parsed) but never consumed by any Ascent equation
/// (semantic dependency groups). Such rules produce parse nodes that are
/// never processed by the semantic layer.
///
/// Severity: Note (informational — the rule may still be needed for pattern matching).
fn lint_d13_ascent_trie_correlation(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    if ctx.semantic_dependency_groups.is_empty() || ctx.decision_trees.is_empty() {
        return;
    }

    // Collect all rule labels referenced by any semantic dependency group
    let semantically_consumed: HashSet<&str> = ctx.semantic_dependency_groups
        .iter()
        .flat_map(|group| group.iter().map(|s| s.as_str()))
        .collect();

    if semantically_consumed.is_empty() {
        return;
    }

    // For each category, find trie-reachable rules not in any semantic group
    for (cat_name, tree) in ctx.decision_trees {
        let reachable = tree.reachable_rules();
        let mut orphans: Vec<&str> = reachable
            .iter()
            .filter(|label| !semantically_consumed.contains(label.as_str()))
            .map(|s| s.as_str())
            .collect();
        orphans.sort_unstable();

        for orphan in &orphans {
            diagnostics.push(LintDiagnostic {
                id: "D13",
                name: "parsed-but-unrewritten",
                severity: LintSeverity::Note,
                category: Some(cat_name.clone()),
                rule: Some(orphan.to_string()),
                message: format!(
                    "rule `{}` is reachable in trie dispatch but appears in zero Ascent equations",
                    orphan,
                ),
                hint: Some(
                    "this constructor is parsed but never semantically consumed; \
                     verify it's needed or add an Ascent equation referencing it"
                        .to_string(),
                ),
                grammar_name: Some(ctx.grammar_name.to_string()),
                source_location: None,
            });
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Mathematical Analysis Lints
// ══════════════════════════════════════════════════════════════════════════════

// ── TRS analysis lints (T01-T04) ────────────────────────────────────────────

#[cfg(feature = "trs-analysis")]
fn lint_t01_non_joinable_critical_pair(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let analysis = match ctx.confluence_result {
        Some(a) => a,
        None => return,
    };
    for (i, cp) in analysis.critical_pairs.iter().enumerate() {
        if matches!(
            analysis.joinability_results.get(i),
            Some(crate::confluence::JoinabilityResult::NotJoinable { .. })
        ) {
            diagnostics.push(LintDiagnostic {
                id: "T01",
                name: "non-joinable-critical-pair",
                severity: LintSeverity::Warning,
                category: None,
                rule: None,
                message: format!(
                    "critical pair (rules {}, {}) is not joinable — confluence failure: {} ≠ {}",
                    cp.rule1_index, cp.rule2_index, cp.term1, cp.term2,
                ),
                hint: Some(
                    "add an equation or oriented rewrite to make the terms joinable"
                        .to_string(),
                ),
                grammar_name: Some(ctx.grammar_name.to_string()),
                source_location: None,
            });
        }
    }
}

#[cfg(feature = "trs-analysis")]
fn lint_t02_confluence_verified(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let analysis = match ctx.confluence_result {
        Some(a) => a,
        None => return,
    };
    if analysis.is_confluent {
        diagnostics.push(LintDiagnostic {
            id: "T02",
            name: "confluence-verified",
            severity: LintSeverity::Note,
            category: None,
            rule: None,
            message: format!(
                "all {} critical pairs are joinable — system is confluent",
                analysis.critical_pairs.len(),
            ),
            hint: None,
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

#[cfg(feature = "trs-analysis")]
fn lint_t03_non_terminating_cycle(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let result = match ctx.termination_result {
        Some(r) => r,
        None => return,
    };
    if let crate::termination::TerminationResult::PotentiallyNonTerminating {
        reason,
        problematic_sccs,
    } = result
    {
        diagnostics.push(LintDiagnostic {
            id: "T03",
            name: "non-terminating-cycle",
            severity: LintSeverity::Warning,
            category: None,
            rule: None,
            message: format!(
                "potential non-termination: {} ({} problematic SCC(s))",
                reason,
                problematic_sccs.len(),
            ),
            hint: Some(
                "add a decreasing measure or simplify the rewrite cycle".to_string(),
            ),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

#[cfg(feature = "trs-analysis")]
fn lint_t04_termination_verified(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let result = match ctx.termination_result {
        Some(r) => r,
        None => return,
    };
    if matches!(result, crate::termination::TerminationResult::Terminating) {
        diagnostics.push(LintDiagnostic {
            id: "T04",
            name: "termination-verified",
            severity: LintSeverity::Note,
            category: None,
            rule: None,
            message: "all SCCs have decreasing measures — system terminates".to_string(),
            hint: None,
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

// ── VPA lints (V01-V02) ─────────────────────────────────────────────────────

#[cfg(feature = "vpa")]
fn lint_v01_vpa_determinizable(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let analysis = match ctx.vpa_result {
        Some(a) => a,
        None => return,
    };
    if analysis.is_determinizable {
        diagnostics.push(LintDiagnostic {
            id: "V01",
            name: "vpa-determinizable",
            severity: LintSeverity::Note,
            category: None,
            rule: None,
            message: format!(
                "grammar's structured sublanguage admits zero-backtracking VPA ({} states)",
                analysis.state_count,
            ),
            hint: None,
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

#[cfg(feature = "vpa")]
fn lint_v02_vpa_alphabet_mismatch(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let analysis = match ctx.vpa_result {
        Some(a) => a,
        None => return,
    };
    for mismatch in &analysis.alphabet_mismatches {
        diagnostics.push(LintDiagnostic {
            id: "V02",
            name: "vpa-alphabet-mismatch",
            severity: LintSeverity::Warning,
            category: None,
            rule: None,
            message: format!(
                "delimiter classification inconsistency: token `{}` classified as both call and return",
                mismatch,
            ),
            hint: Some(
                "ensure each delimiter token is used consistently as either opening or closing"
                    .to_string(),
            ),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

// ── WTA lints (V03-V04) ─────────────────────────────────────────────────────

#[cfg(feature = "tree-automata")]
fn lint_v03_wta_unrecognized_term(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let analysis = match ctx.wta_result {
        Some(a) => a,
        None => return,
    };
    for term in &analysis.unrecognized_terms {
        diagnostics.push(LintDiagnostic {
            id: "V03",
            name: "wta-unrecognized-term",
            severity: LintSeverity::Warning,
            category: None,
            rule: None,
            message: format!(
                "term pattern `{}` not in regular tree language",
                term,
            ),
            hint: Some(
                "add a rule or transition to recognize this term pattern".to_string(),
            ),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

#[cfg(feature = "tree-automata")]
fn lint_v04_wta_hot_path(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let analysis = match ctx.wta_result {
        Some(a) => a,
        None => return,
    };
    for path in &analysis.hot_paths {
        diagnostics.push(LintDiagnostic {
            id: "V04",
            name: "wta-hot-path",
            severity: LintSeverity::Note,
            category: None,
            rule: None,
            message: format!(
                "frequently weighted term pattern: {} — specialization candidate",
                path,
            ),
            hint: None,
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

// ── Safety verification lints (S01-S06) ─────────────────────────────────────

fn lint_s01_safety_violation(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let result = match ctx.safety_result {
        Some(r) => r,
        None => return,
    };
    if !result.safe {
        diagnostics.push(LintDiagnostic {
            id: "S01",
            name: "safety-violation",
            severity: LintSeverity::Warning,
            category: None,
            rule: None,
            message: format!(
                "bad state reachable via WPDS prestar (initial weight: {})",
                result.initial_weight,
            ),
            hint: Some(
                "review the grammar for unreachable-yet-dispatched rules".to_string(),
            ),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

fn lint_s02_safety_verified(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let result = match ctx.safety_result {
        Some(r) => r,
        None => return,
    };
    if result.safe {
        diagnostics.push(LintDiagnostic {
            id: "S02",
            name: "safety-verified",
            severity: LintSeverity::Note,
            category: None,
            rule: None,
            message: "no bad states reachable — safety property verified".to_string(),
            hint: None,
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

fn lint_s03_cegar_refinement(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let log = match ctx.cegar_result {
        Some(l) => l,
        None => return,
    };
    let final_verdict = log
        .steps
        .last()
        .map(|s| format!("{}", s.verdict))
        .unwrap_or_else(|| "unknown".to_string());
    diagnostics.push(LintDiagnostic {
        id: "S03",
        name: "cegar-refinement",
        severity: LintSeverity::Note,
        category: None,
        rule: None,
        message: format!(
            "CEGAR loop: {} refinement step(s), final verdict: {}",
            log.steps.len(),
            final_verdict,
        ),
        hint: None,
        grammar_name: Some(ctx.grammar_name.to_string()),
        source_location: None,
    });
}

#[cfg(feature = "wpds-extended")]
fn lint_s04_ewpds_merge_site(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let result = match ctx.ewpds_result {
        Some(r) => r,
        None => return,
    };
    if result.merge_site_count > 0 {
        diagnostics.push(LintDiagnostic {
            id: "S04",
            name: "ewpds-merge-site",
            severity: LintSeverity::Note,
            category: None,
            rule: None,
            message: format!(
                "identified {} merge function site(s): {}",
                result.merge_site_count,
                result.merge_site_labels.join(", "),
            ),
            hint: None,
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

#[cfg(feature = "wpds-ara")]
fn lint_s05_ara_invariant(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let result = match ctx.ara_result {
        Some(r) => r,
        None => return,
    };
    diagnostics.push(LintDiagnostic {
        id: "S05",
        name: "ara-invariant",
        severity: LintSeverity::Note,
        category: None,
        rule: None,
        message: format!(
            "ARA weight domain: dimension={}, {} invariant(s) discovered",
            result.dimension, result.invariant_count,
        ),
        hint: None,
        grammar_name: Some(ctx.grammar_name.to_string()),
        source_location: None,
    });
}

fn lint_s06_algebraic_summary(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let result = match ctx.algebraic_result {
        Some(r) => r,
        None => return,
    };
    diagnostics.push(LintDiagnostic {
        id: "S06",
        name: "algebraic-summary",
        severity: LintSeverity::Note,
        category: None,
        rule: None,
        message: format!(
            "Tarjan path expression summary: {} SCC(s), {} expression(s)",
            result.scc_count, result.path_expression_count,
        ),
        hint: None,
        grammar_name: Some(ctx.grammar_name.to_string()),
        source_location: None,
    });
}

// ── Concurrency lints (N01-N05) ─────────────────────────────────────────────

#[cfg(feature = "petri")]
fn lint_n01_deadlock_risk(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let result = match ctx.petri_result {
        Some(r) => r,
        None => return,
    };
    if result.has_deadlock_risk {
        diagnostics.push(LintDiagnostic {
            id: "N01",
            name: "deadlock-risk",
            severity: LintSeverity::Warning,
            category: None,
            rule: None,
            message: format!(
                "Petri net coverability detects potential deadlock ({} places, {} transitions)",
                result.place_count, result.transition_count,
            ),
            hint: Some(
                "review parallel composition operators for potential blocking patterns"
                    .to_string(),
            ),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

#[cfg(feature = "petri")]
fn lint_n02_unbounded_channel(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let result = match ctx.petri_result {
        Some(r) => r,
        None => return,
    };
    for place in &result.unbounded_places {
        diagnostics.push(LintDiagnostic {
            id: "N02",
            name: "unbounded-channel",
            severity: LintSeverity::Warning,
            category: None,
            rule: None,
            message: format!(
                "place `{}` has unbounded token capacity",
                place,
            ),
            hint: Some(
                "consider adding a capacity bound to prevent resource exhaustion"
                    .to_string(),
            ),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

#[cfg(feature = "nominal")]
fn lint_n03_scope_violation(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let result = match ctx.nominal_result {
        Some(r) => r,
        None => return,
    };
    for (name, context) in &result.scope_violations {
        diagnostics.push(LintDiagnostic {
            id: "N03",
            name: "scope-violation",
            severity: LintSeverity::Warning,
            category: None,
            rule: None,
            message: format!(
                "name `{}` used outside its binding scope ({})",
                name, context,
            ),
            hint: Some(
                "ensure the name is only used within the scope of its binder".to_string(),
            ),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

#[cfg(feature = "nominal")]
fn lint_n04_scope_narrowing(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let result = match ctx.nominal_result {
        Some(r) => r,
        None => return,
    };
    for (binder, suggestion) in &result.narrowing_candidates {
        diagnostics.push(LintDiagnostic {
            id: "N04",
            name: "scope-narrowing",
            severity: LintSeverity::Note,
            category: None,
            rule: None,
            message: format!(
                "`PNew` scope for binder `{}` can be tightened: {}",
                binder, suggestion,
            ),
            hint: None,
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

#[cfg(feature = "alternating")]
fn lint_n05_non_bisimilar(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let result = match ctx.alternating_result {
        Some(r) => r,
        None => return,
    };
    for (cat_a, cat_b) in &result.non_bisimilar_pairs {
        diagnostics.push(LintDiagnostic {
            id: "N05",
            name: "non-bisimilar",
            severity: LintSeverity::Warning,
            category: None,
            rule: None,
            message: format!(
                "categories `{}` and `{}` are not bisimilar (attacker wins game)",
                cat_a, cat_b,
            ),
            hint: Some(
                "these categories have structurally different observable behavior"
                    .to_string(),
            ),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

// ── Temporal lints (L01-L02) ────────────────────────────────────────────────

#[cfg(feature = "ltl")]
fn lint_l01_ltl_violated(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let results = match ctx.ltl_results {
        Some(r) => r,
        None => return,
    };
    for (i, result) in results.iter().enumerate() {
        if let crate::ltl::LtlCheckResult::Violated { prefix, .. } = result {
            let desc = prefix.first().map(|s| s.as_str()).unwrap_or("unknown");
            diagnostics.push(LintDiagnostic {
                id: "L01",
                name: "ltl-violated",
                severity: LintSeverity::Warning,
                category: None,
                rule: None,
                message: format!(
                    "LTL property #{} violated (Buchi product non-empty): {}",
                    i, desc,
                ),
                hint: Some(
                    "the grammar's execution traces can violate this temporal property"
                        .to_string(),
                ),
                grammar_name: Some(ctx.grammar_name.to_string()),
                source_location: None,
            });
        }
    }
}

#[cfg(feature = "ltl")]
fn lint_l02_ltl_verified(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let results = match ctx.ltl_results {
        Some(r) => r,
        None => return,
    };
    let satisfied_count = results
        .iter()
        .filter(|r| matches!(r, crate::ltl::LtlCheckResult::Satisfied))
        .count();
    if satisfied_count > 0 {
        diagnostics.push(LintDiagnostic {
            id: "L02",
            name: "ltl-verified",
            severity: LintSeverity::Note,
            category: None,
            rule: None,
            message: format!(
                "{} LTL propert{} satisfied",
                satisfied_count,
                if satisfied_count == 1 { "y" } else { "ies" },
            ),
            hint: None,
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

// ── Extension lints (E01-E02) ───────────────────────────────────────────────

#[cfg(feature = "provenance")]
fn lint_e01_provenance_trace(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let result = match ctx.provenance_result {
        Some(r) => r,
        None => return,
    };
    if !result.provenance_traces.is_empty() {
        diagnostics.push(LintDiagnostic {
            id: "E01",
            name: "provenance-trace",
            severity: LintSeverity::Note,
            category: None,
            rule: None,
            message: format!(
                "how-provenance: {} polynomial(s) computed",
                result.provenance_traces.len(),
            ),
            hint: None,
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

#[cfg(feature = "cra")]
fn lint_e02_cra_cost_anomaly(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let result = match ctx.cra_result {
        Some(r) => r,
        None => return,
    };
    for (desc, value) in &result.cost_anomalies {
        diagnostics.push(LintDiagnostic {
            id: "E02",
            name: "cra-cost-anomaly",
            severity: LintSeverity::Warning,
            category: None,
            rule: None,
            message: format!(
                "CRA register value exceeds threshold: {} = {}",
                desc, value,
            ),
            hint: Some(
                "review the grammar's quantitative cost model".to_string(),
            ),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

// ── Morphism lints (M01-M02) ────────────────────────────────────────────────

#[cfg(feature = "morphisms")]
fn lint_m01_morphism_gap(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let result = match ctx.morphism_result {
        Some(r) => r,
        None => return,
    };
    for gap in &result.gaps {
        diagnostics.push(LintDiagnostic {
            id: "M01",
            name: "morphism-gap",
            severity: LintSeverity::Warning,
            category: None,
            rule: None,
            message: format!(
                "theory morphism incomplete — missing constructor mapping: {}",
                gap,
            ),
            hint: Some(
                "add a cross-category rule or constructor to complete the morphism"
                    .to_string(),
            ),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

#[cfg(feature = "morphisms")]
fn lint_m02_morphism_preservation_failure(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let result = match ctx.morphism_result {
        Some(r) => r,
        None => return,
    };
    for failure in &result.preservation_failures {
        diagnostics.push(LintDiagnostic {
            id: "M02",
            name: "morphism-preservation-failure",
            severity: LintSeverity::Warning,
            category: None,
            rule: None,
            message: format!(
                "equation not preserved under morphism: {}",
                failure,
            ),
            hint: Some(
                "the morphism does not preserve this algebraic equation".to_string(),
            ),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

// ── KAT lints (K01-K02) ────────────────────────────────────────────────────

#[cfg(feature = "kat")]
fn lint_k01_hoare_failure(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let result = match ctx.kat_result {
        Some(r) => r,
        None => return,
    };
    for (desc, passed) in &result.hoare_results {
        if !passed {
            diagnostics.push(LintDiagnostic {
                id: "K01",
                name: "hoare-failure",
                severity: LintSeverity::Warning,
                category: None,
                rule: None,
                message: format!(
                    "Hoare triple failed: {}",
                    desc,
                ),
                hint: Some(
                    "p·e·¬q ≠ 0 — the program does not satisfy its specification"
                        .to_string(),
                ),
                grammar_name: Some(ctx.grammar_name.to_string()),
                source_location: None,
            });
        }
    }
}

#[cfg(feature = "kat")]
fn lint_k02_kat_equivalence(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let result = match ctx.kat_result {
        Some(r) => r,
        None => return,
    };
    for (expr1, expr2, equivalent) in &result.equivalence_results {
        diagnostics.push(LintDiagnostic {
            id: "K02",
            name: "kat-equivalence",
            severity: LintSeverity::Note,
            category: None,
            rule: None,
            message: format!(
                "KAT equivalence: {} {} {}",
                expr1,
                if *equivalent { "≡" } else { "≢" },
                expr2,
            ),
            hint: None,
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

// ── Pipeline timing lint (P06) ──────────────────────────────────────────────

fn lint_p06_analysis_pipeline_cost(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let elapsed = match ctx.math_analysis_elapsed {
        Some(d) => d,
        None => return,
    };
    // Only emit if there's meaningful work done (> 100µs)
    if elapsed.as_micros() < 100 {
        return;
    }
    diagnostics.push(LintDiagnostic {
        id: "P06",
        name: "analysis-pipeline-cost",
        severity: LintSeverity::Note,
        category: None,
        rule: None,
        message: format!(
            "mathematical analysis phase completed in {:.2}ms",
            elapsed.as_secs_f64() * 1000.0,
        ),
        hint: None,
        grammar_name: Some(ctx.grammar_name.to_string()),
        source_location: None,
    });
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use crate::binding_power::{BindingPowerTable, InfixOperator};
    use crate::dispatch::{CastRule, CrossCategoryRule};
    use crate::pipeline::CategoryInfo;
    use crate::prediction::{FirstItem, FirstSet, FollowSetInput, RuleInfo};
    use crate::recovery::RecoveryConfig;
    use crate::recursive::RDRuleInfo;

    // ── Helper constructors ──

    fn cat_info(name: &str, native_type: Option<&str>, is_primary: bool) -> CategoryInfo {
        CategoryInfo {
            name: name.to_string(),
            native_type: native_type.map(|s| s.to_string()),
            is_primary,
        }
    }

    fn make_rule_info(
        label: &str,
        category: &str,
        first_items: Vec<FirstItem>,
        is_infix: bool,
    ) -> RuleInfo {
        RuleInfo {
            label: label.to_string(),
            category: category.to_string(),
            first_items,
            is_infix,
            is_var: false,
            is_literal: false,
            is_cross_category: false,
            is_cast: false,
        }
    }

    /// Minimal context builder for quick tests.
    struct CtxBuilder {
        grammar_name: String,
        rule_locations: HashMap<(String, String), crate::SourceLocation>,
        categories: Vec<CategoryInfo>,
        rules: Vec<RuleInfo>,
        rd_rules: Vec<RDRuleInfo>,
        first_sets: HashMap<String, FirstSet>,
        follow_sets: HashMap<String, FirstSet>,
        bp_table: BindingPowerTable,
        prediction_wfsts: HashMap<String, PredictionWfst>,
        recovery_wfsts: Vec<RecoveryWfst>,
        cast_rules: Vec<CastRule>,
        cross_rules: Vec<CrossCategoryRule>,
        nfa_spillover_categories: HashSet<String>,
        recovery_config: RecoveryConfig,
        all_syntax: Vec<(String, String, Vec<SyntaxItemSpec>)>,
        follow_inputs: Vec<FollowSetInput>,
        semantic_dependency_groups: Vec<HashSet<String>>,
        pre_collected_diagnostics: Vec<LintDiagnostic>,
        decision_trees: HashMap<String, CategoryDecisionTree>,
        token_id_map: TokenIdMap,
        dead_rule_warnings: Vec<crate::pipeline::DeadRuleWarning>,
        // ── Mathematical analysis result fields ──
        safety_result_data: Option<crate::verify::SafetyResult<crate::automata::semiring::BooleanWeight>>,
        cegar_result_data: Option<crate::cegar::CegarLog>,
        algebraic_result_data: Option<crate::algebraic::AlgebraicSummary>,
        math_analysis_elapsed_data: Option<std::time::Duration>,
        #[cfg(feature = "trs-analysis")]
        confluence_result_data: Option<crate::confluence::ConfluenceAnalysis>,
        #[cfg(feature = "trs-analysis")]
        termination_result_data: Option<crate::termination::TerminationResult>,
        #[cfg(feature = "vpa")]
        vpa_result_data: Option<crate::vpa::VpaAnalysis>,
        #[cfg(feature = "tree-automata")]
        wta_result_data: Option<crate::tree_automaton::WtaAnalysis>,
        #[cfg(feature = "wpds-extended")]
        ewpds_result_data: Option<crate::ewpds::EwpdsAnalysis>,
        #[cfg(feature = "wpds-ara")]
        ara_result_data: Option<crate::ara::AraAnalysis>,
        #[cfg(feature = "petri")]
        petri_result_data: Option<crate::petri::PetriAnalysis>,
        #[cfg(feature = "nominal")]
        nominal_result_data: Option<crate::nominal::NominalAnalysis>,
        #[cfg(feature = "alternating")]
        alternating_result_data: Option<crate::alternating::AlternatingAnalysis>,
        #[cfg(feature = "ltl")]
        ltl_results_data: Option<Vec<crate::ltl::LtlCheckResult>>,
        #[cfg(feature = "provenance")]
        provenance_result_data: Option<crate::provenance::ProvenanceAnalysis>,
        #[cfg(feature = "cra")]
        cra_result_data: Option<crate::cra::CraAnalysis>,
        #[cfg(feature = "morphisms")]
        morphism_result_data: Option<crate::morphism::MorphismCheck>,
        #[cfg(feature = "kat")]
        kat_result_data: Option<crate::kat::KatCheck>,
    }

    impl CtxBuilder {
        fn new() -> Self {
            CtxBuilder {
                grammar_name: "TestGrammar".to_string(),
                rule_locations: HashMap::new(),
                categories: Vec::new(),
                rules: Vec::new(),
                rd_rules: Vec::new(),
                first_sets: HashMap::new(),
                follow_sets: HashMap::new(),
                bp_table: BindingPowerTable::new(),
                prediction_wfsts: HashMap::new(),
                recovery_wfsts: Vec::new(),
                cast_rules: Vec::new(),
                cross_rules: Vec::new(),
                nfa_spillover_categories: HashSet::new(),
                recovery_config: RecoveryConfig::default(),
                all_syntax: Vec::new(),
                follow_inputs: Vec::new(),
                semantic_dependency_groups: Vec::new(),
                pre_collected_diagnostics: Vec::new(),
                decision_trees: HashMap::new(),
                token_id_map: TokenIdMap::new(),
                dead_rule_warnings: Vec::new(),
                // ── Mathematical analysis result fields ──
                safety_result_data: None,
                cegar_result_data: None,
                algebraic_result_data: None,
                math_analysis_elapsed_data: None,
                #[cfg(feature = "trs-analysis")]
                confluence_result_data: None,
                #[cfg(feature = "trs-analysis")]
                termination_result_data: None,
                #[cfg(feature = "vpa")]
                vpa_result_data: None,
                #[cfg(feature = "tree-automata")]
                wta_result_data: None,
                #[cfg(feature = "wpds-extended")]
                ewpds_result_data: None,
                #[cfg(feature = "wpds-ara")]
                ara_result_data: None,
                #[cfg(feature = "petri")]
                petri_result_data: None,
                #[cfg(feature = "nominal")]
                nominal_result_data: None,
                #[cfg(feature = "alternating")]
                alternating_result_data: None,
                #[cfg(feature = "ltl")]
                ltl_results_data: None,
                #[cfg(feature = "provenance")]
                provenance_result_data: None,
                #[cfg(feature = "cra")]
                cra_result_data: None,
                #[cfg(feature = "morphisms")]
                morphism_result_data: None,
                #[cfg(feature = "kat")]
                kat_result_data: None,
            }
        }

        fn ctx(&self) -> LintContext<'_> {
            LintContext {
                grammar_name: &self.grammar_name,
                rule_locations: &self.rule_locations,
                categories: &self.categories,
                rules: &self.rules,
                rd_rules: &self.rd_rules,
                first_sets: &self.first_sets,
                follow_sets: &self.follow_sets,
                bp_table: &self.bp_table,
                prediction_wfsts: &self.prediction_wfsts,
                recovery_wfsts: &self.recovery_wfsts,
                cast_rules: &self.cast_rules,
                cross_rules: &self.cross_rules,
                nfa_spillover_categories: &self.nfa_spillover_categories,
                recovery_config: &self.recovery_config,
                all_syntax: &self.all_syntax,
                follow_inputs: &self.follow_inputs,
                semantic_dependency_groups: &self.semantic_dependency_groups,
                pre_collected_diagnostics: &self.pre_collected_diagnostics,
                decision_trees: &self.decision_trees,
                token_id_map: &self.token_id_map,
                dead_rule_warnings: &self.dead_rule_warnings,
                grammar_profile: None,
                wpds_analysis: None,
                wpds_elapsed: None,
                // ── Mathematical analysis results ──
                safety_result: self.safety_result_data.as_ref(),
                cegar_result: self.cegar_result_data.as_ref(),
                algebraic_result: self.algebraic_result_data.as_ref(),
                math_analysis_elapsed: self.math_analysis_elapsed_data,
                #[cfg(feature = "trs-analysis")]
                confluence_result: self.confluence_result_data.as_ref(),
                #[cfg(feature = "trs-analysis")]
                termination_result: self.termination_result_data.as_ref(),
                #[cfg(feature = "vpa")]
                vpa_result: self.vpa_result_data.as_ref(),
                #[cfg(feature = "tree-automata")]
                wta_result: self.wta_result_data.as_ref(),
                #[cfg(feature = "wpds-extended")]
                ewpds_result: self.ewpds_result_data.as_ref(),
                #[cfg(feature = "wpds-ara")]
                ara_result: self.ara_result_data.as_ref(),
                #[cfg(feature = "petri")]
                petri_result: self.petri_result_data.as_ref(),
                #[cfg(feature = "nominal")]
                nominal_result: self.nominal_result_data.as_ref(),
                #[cfg(feature = "alternating")]
                alternating_result: self.alternating_result_data.as_ref(),
                #[cfg(feature = "ltl")]
                ltl_results: self.ltl_results_data.as_ref(),
                #[cfg(feature = "provenance")]
                provenance_result: self.provenance_result_data.as_ref(),
                #[cfg(feature = "cra")]
                cra_result: self.cra_result_data.as_ref(),
                #[cfg(feature = "morphisms")]
                morphism_result: self.morphism_result_data.as_ref(),
                #[cfg(feature = "kat")]
                kat_result: self.kat_result_data.as_ref(),
            }
        }
    }

    // ══════════════════════════════════════════════════════════════════════
    // G01: Left Recursion
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn g01_fires_on_left_recursive_rd_rule() {
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Int", None, true));
        b.all_syntax.push((
            "BadRule".to_string(),
            "Int".to_string(),
            vec![
                SyntaxItemSpec::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "a".to_string(),
                },
                SyntaxItemSpec::Terminal("@".to_string()),
                SyntaxItemSpec::Terminal("#".to_string()),
            ],
        ));

        let mut diags = Vec::new();
        lint_g01_left_recursion(&b.ctx(), &mut diags);

        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, "G01");
        assert_eq!(diags[0].severity, LintSeverity::Warning);
    }

    #[test]
    fn g01_skips_infix_pattern() {
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Int", None, true));
        b.all_syntax.push((
            "Add".to_string(),
            "Int".to_string(),
            vec![
                SyntaxItemSpec::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "a".to_string(),
                },
                SyntaxItemSpec::Terminal("+".to_string()),
                SyntaxItemSpec::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "b".to_string(),
                },
            ],
        ));

        let mut diags = Vec::new();
        lint_g01_left_recursion(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }

    // ══════════════════════════════════════════════════════════════════════
    // G02: Unused Category
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn g02_fires_on_unreferenced_category() {
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Int", None, true));
        b.categories.push(cat_info("Unused", None, false));
        b.all_syntax
            .push(("NumLit".to_string(), "Int".to_string(), vec![]));

        let mut diags = Vec::new();
        lint_g02_unused_category(&b.ctx(), &mut diags);

        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, "G02");
        assert!(diags[0].message.contains("Unused"));
    }

    #[test]
    fn g02_does_not_fire_when_referenced() {
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Int", None, true));
        b.all_syntax
            .push(("NumLit".to_string(), "Int".to_string(), vec![]));

        let mut diags = Vec::new();
        lint_g02_unused_category(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }

    // ══════════════════════════════════════════════════════════════════════
    // G03: Ambiguous Prefix
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn g03_fires_on_same_terminal() {
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Int", None, true));
        b.rules.push(make_rule_info(
            "Foo",
            "Int",
            vec![FirstItem::Terminal("!".to_string())],
            false,
        ));
        b.rules.push(make_rule_info(
            "Bar",
            "Int",
            vec![FirstItem::Terminal("!".to_string())],
            false,
        ));

        let mut diags = Vec::new();
        lint_g03_ambiguous_prefix(&b.ctx(), &mut diags);

        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, "G03");
    }

    #[test]
    fn g03_skips_infix_rules() {
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Int", None, true));
        b.rules.push(make_rule_info(
            "Add",
            "Int",
            vec![FirstItem::Terminal("+".to_string())],
            true,
        ));
        b.rules.push(make_rule_info(
            "Pos",
            "Int",
            vec![FirstItem::Terminal("+".to_string())],
            false,
        ));

        let mut diags = Vec::new();
        lint_g03_ambiguous_prefix(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }

    // ══════════════════════════════════════════════════════════════════════
    // G04: Duplicate Rule Label
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn g04_fires_on_duplicate_label() {
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Int", None, true));
        b.all_syntax.push(("Add".to_string(), "Int".to_string(), vec![]));
        b.all_syntax.push(("Add".to_string(), "Int".to_string(), vec![]));

        let mut diags = Vec::new();
        lint_g04_duplicate_rule_label(&b.ctx(), &mut diags);

        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, "G04");
        assert_eq!(diags[0].severity, LintSeverity::Error);
    }

    #[test]
    fn g04_allows_same_label_different_category() {
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Int", None, true));
        b.categories.push(cat_info("Float", None, false));
        b.all_syntax.push(("Add".to_string(), "Int".to_string(), vec![]));
        b.all_syntax.push(("Add".to_string(), "Float".to_string(), vec![]));

        let mut diags = Vec::new();
        lint_g04_duplicate_rule_label(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }

    // ══════════════════════════════════════════════════════════════════════
    // G05: Empty Category
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn g05_fires_on_empty_category() {
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Int", None, true));
        b.categories.push(cat_info("Empty", None, false));
        b.all_syntax.push(("NumLit".to_string(), "Int".to_string(), vec![]));

        let mut diags = Vec::new();
        lint_g05_empty_category(&b.ctx(), &mut diags);

        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, "G05");
        assert!(diags[0].message.contains("Empty"));
    }

    #[test]
    fn g05_does_not_fire_when_has_rules() {
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Int", None, true));
        b.all_syntax.push(("NumLit".to_string(), "Int".to_string(), vec![]));

        let mut diags = Vec::new();
        lint_g05_empty_category(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }

    #[test]
    fn g05_does_not_fire_for_native_type_category() {
        let mut b = CtxBuilder::new();
        // Category with native_type but zero explicit rules — should NOT trigger G05.
        b.categories.push(cat_info("Int", Some("i64"), true));

        let mut diags = Vec::new();
        lint_g05_empty_category(&b.ctx(), &mut diags);
        assert!(diags.is_empty(), "G05 should not fire for native-type categories");
    }

    // ══════════════════════════════════════════════════════════════════════
    // G07: Identical Rules
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn g07_fires_on_identical_syntax() {
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Int", None, true));
        let syntax = vec![
            SyntaxItemSpec::Terminal("(".to_string()),
            SyntaxItemSpec::NonTerminal {
                category: "Int".to_string(),
                param_name: "a".to_string(),
            },
            SyntaxItemSpec::Terminal(")".to_string()),
        ];
        b.all_syntax
            .push(("Group1".to_string(), "Int".to_string(), syntax.clone()));
        b.all_syntax
            .push(("Group2".to_string(), "Int".to_string(), syntax));

        let mut diags = Vec::new();
        lint_g07_identical_rules(&b.ctx(), &mut diags);

        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, "G07");
    }

    #[test]
    fn g07_does_not_fire_on_different_syntax() {
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Int", None, true));
        b.all_syntax.push((
            "Neg".to_string(),
            "Int".to_string(),
            vec![
                SyntaxItemSpec::Terminal("-".to_string()),
                SyntaxItemSpec::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "a".to_string(),
                },
            ],
        ));
        b.all_syntax.push((
            "Not".to_string(),
            "Int".to_string(),
            vec![
                SyntaxItemSpec::Terminal("~".to_string()),
                SyntaxItemSpec::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "a".to_string(),
                },
            ],
        ));

        let mut diags = Vec::new();
        lint_g07_identical_rules(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }

    // ══════════════════════════════════════════════════════════════════════
    // G08: Missing Cast to Root
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn g08_fires_when_no_cast_path() {
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Proc", None, true));
        b.categories.push(cat_info("Int", None, false));
        // No cast rules from Int to Proc

        let mut diags = Vec::new();
        lint_g08_missing_cast_to_root(&b.ctx(), &mut diags);

        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, "G08");
        assert!(diags[0].message.contains("Int"));
    }

    #[test]
    fn g08_does_not_fire_with_cast_path() {
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Proc", None, true));
        b.categories.push(cat_info("Int", None, false));
        b.cast_rules.push(CastRule {
            label: "IntToProc".to_string(),
            source_category: "Int".to_string(),
            target_category: "Proc".to_string(),
        });

        let mut diags = Vec::new();
        lint_g08_missing_cast_to_root(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }

    // ══════════════════════════════════════════════════════════════════════
    // G09: Unbalanced Delimiters
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn g09_fires_on_unbalanced() {
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Int", None, true));
        b.all_syntax.push((
            "Bad".to_string(),
            "Int".to_string(),
            vec![
                SyntaxItemSpec::Terminal("(".to_string()),
                SyntaxItemSpec::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "a".to_string(),
                },
                // Missing ")"
            ],
        ));

        let mut diags = Vec::new();
        lint_g09_unbalanced_delimiters(&b.ctx(), &mut diags);

        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, "G09");
    }

    #[test]
    fn g09_does_not_fire_on_balanced() {
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Int", None, true));
        b.all_syntax.push((
            "Group".to_string(),
            "Int".to_string(),
            vec![
                SyntaxItemSpec::Terminal("(".to_string()),
                SyntaxItemSpec::NonTerminal {
                    category: "Int".to_string(),
                    param_name: "a".to_string(),
                },
                SyntaxItemSpec::Terminal(")".to_string()),
            ],
        ));

        let mut diags = Vec::new();
        lint_g09_unbalanced_delimiters(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }

    #[test]
    fn g09_compound_terminal_no_false_positive() {
        // "in(" contributes 1 open paren; paired with standalone ")" → balanced
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Proc", None, true));
        b.all_syntax.push((
            "PIn".to_string(),
            "Proc".to_string(),
            vec![
                SyntaxItemSpec::Terminal("in(".to_string()),
                SyntaxItemSpec::NonTerminal {
                    category: "Proc".to_string(),
                    param_name: "x".to_string(),
                },
                SyntaxItemSpec::Terminal(")".to_string()),
            ],
        ));

        let mut diags = Vec::new();
        lint_g09_unbalanced_delimiters(&b.ctx(), &mut diags);
        assert!(
            diags.is_empty(),
            "compound terminal `in(` paired with `)` should be balanced: {:?}",
            diags,
        );
    }

    #[test]
    fn g09_compound_terminal_true_positive() {
        // "in(" with no closing paren → unbalanced
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Proc", None, true));
        b.all_syntax.push((
            "PIn".to_string(),
            "Proc".to_string(),
            vec![
                SyntaxItemSpec::Terminal("in(".to_string()),
                SyntaxItemSpec::NonTerminal {
                    category: "Proc".to_string(),
                    param_name: "x".to_string(),
                },
            ],
        ));

        let mut diags = Vec::new();
        lint_g09_unbalanced_delimiters(&b.ctx(), &mut diags);
        assert_eq!(diags.len(), 1, "compound terminal `in(` without `)` should be unbalanced");
        assert_eq!(diags[0].id, "G09");
    }

    #[test]
    fn g09_self_balanced_terminal() {
        // "()" is self-balanced — 1 open + 1 close = balanced
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Proc", None, true));
        b.all_syntax.push((
            "PNil".to_string(),
            "Proc".to_string(),
            vec![SyntaxItemSpec::Terminal("()".to_string())],
        ));

        let mut diags = Vec::new();
        lint_g09_unbalanced_delimiters(&b.ctx(), &mut diags);
        assert!(
            diags.is_empty(),
            "self-balanced `()` terminal should not trigger G09: {:?}",
            diags,
        );
    }

    // ══════════════════════════════════════════════════════════════════════
    // G10: Ambiguous Associativity
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn g10_fires_on_mixed_associativity() {
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Int", None, true));
        b.bp_table.operators.push(InfixOperator {
            terminal: "+".to_string(),
            category: "Int".to_string(),
            result_category: "Int".to_string(),
            left_bp: 2,
            right_bp: 3,
            label: "Add".to_string(),
            is_cross_category: false,
            is_postfix: false,
            is_mixfix: false,
            mixfix_parts: vec![],
        });
        b.bp_table.operators.push(InfixOperator {
            terminal: "-".to_string(),
            category: "Int".to_string(),
            result_category: "Int".to_string(),
            left_bp: 2,
            right_bp: 1, // Right-associative at same left_bp
            label: "Sub".to_string(),
            is_cross_category: false,
            is_postfix: false,
            is_mixfix: false,
            mixfix_parts: vec![],
        });

        let mut diags = Vec::new();
        lint_g10_ambiguous_associativity(&b.ctx(), &mut diags);

        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, "G10");
    }

    #[test]
    fn g10_does_not_fire_on_same_associativity() {
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Int", None, true));
        b.bp_table.operators.push(InfixOperator {
            terminal: "+".to_string(),
            category: "Int".to_string(),
            result_category: "Int".to_string(),
            left_bp: 2,
            right_bp: 3,
            label: "Add".to_string(),
            is_cross_category: false,
            is_postfix: false,
            is_mixfix: false,
            mixfix_parts: vec![],
        });
        b.bp_table.operators.push(InfixOperator {
            terminal: "-".to_string(),
            category: "Int".to_string(),
            result_category: "Int".to_string(),
            left_bp: 2,
            right_bp: 3, // Same left-assoc
            label: "Sub".to_string(),
            is_cross_category: false,
            is_postfix: false,
            is_mixfix: false,
            mixfix_parts: vec![],
        });

        let mut diags = Vec::new();
        lint_g10_ambiguous_associativity(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }

    // ══════════════════════════════════════════════════════════════════════
    // R06: Inverted Recovery Costs
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn r06_fires_on_inverted_costs() {
        let mut b = CtxBuilder::new();
        b.recovery_config.skip_per_token = 3.0; // Higher than insert!
        b.recovery_config.insert_cost = 1.0;

        let mut diags = Vec::new();
        lint_r06_inverted_recovery_costs(&b.ctx(), &mut diags);

        assert!(diags.iter().any(|d| d.id == "R06"));
    }

    #[test]
    fn r06_does_not_fire_on_default_config() {
        let b = CtxBuilder::new();

        let mut diags = Vec::new();
        lint_r06_inverted_recovery_costs(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }

    // ══════════════════════════════════════════════════════════════════════
    // R07: Transposition Candidate
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn r07_fires_on_edit_distance_one() {
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Int", None, true));
        b.all_syntax.push((
            "Add".to_string(),
            "Int".to_string(),
            vec![SyntaxItemSpec::Terminal("+".to_string())],
        ));
        b.all_syntax.push((
            "Inc".to_string(),
            "Int".to_string(),
            vec![SyntaxItemSpec::Terminal("++".to_string())],
        ));

        let mut diags = Vec::new();
        lint_r07_transposition_candidate(&b.ctx(), &mut diags);

        assert_eq!(diags.len(), 1, "R07 should emit exactly 1 summary note");
        assert_eq!(diags[0].id, "R07");
        assert!(diags[0].message.contains("1 operator pair(s)"));
        assert!(diags[0].message.contains("`+`"));
        assert!(diags[0].message.contains("`++`"));
    }

    #[test]
    fn r07_does_not_fire_on_distant_operators() {
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Int", None, true));
        b.all_syntax.push((
            "Add".to_string(),
            "Int".to_string(),
            vec![SyntaxItemSpec::Terminal("++".to_string())],
        ));
        b.all_syntax.push((
            "Arrow".to_string(),
            "Int".to_string(),
            vec![SyntaxItemSpec::Terminal("->".to_string())],
        ));

        let mut diags = Vec::new();
        lint_r07_transposition_candidate(&b.ctx(), &mut diags);
        assert!(diags.is_empty(), "operators `++` and `->` differ by 2 chars: {:?}", diags);
    }

    #[test]
    fn r07_many_single_char_operators_single_summary() {
        // 9 single-char operators → C(9,2)=36 pairs all at distance 1 (all single-char
        // operators differ by exactly 1 substitution). Should emit exactly 1 summary.
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Int", None, true));
        for (i, op) in ["!", "@", "#", "$", "%", "^", "&", "*", "~"].iter().enumerate() {
            b.all_syntax.push((
                format!("Op{}", i),
                "Int".to_string(),
                vec![SyntaxItemSpec::Terminal(op.to_string())],
            ));
        }

        let mut diags = Vec::new();
        lint_r07_transposition_candidate(&b.ctx(), &mut diags);

        assert_eq!(
            diags.len(),
            1,
            "R07 should emit exactly 1 summary note, not {} individual notes",
            diags.len(),
        );
        assert_eq!(diags[0].id, "R07");
        // The summary should mention the total count (36 pairs)
        assert!(
            diags[0].message.contains("36 operator pair(s)"),
            "message should contain total pair count: {}",
            diags[0].message,
        );
    }

    // ══════════════════════════════════════════════════════════════════════
    // C01: Cast Cycle
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn c01_fires_on_cycle() {
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Int", None, true));
        b.categories.push(cat_info("Proc", None, false));
        b.cast_rules.push(CastRule {
            label: "IntToProc".to_string(),
            source_category: "Int".to_string(),
            target_category: "Proc".to_string(),
        });
        b.cast_rules.push(CastRule {
            label: "ProcToInt".to_string(),
            source_category: "Proc".to_string(),
            target_category: "Int".to_string(),
        });

        let mut diags = Vec::new();
        lint_c01_cast_cycle(&b.ctx(), &mut diags);

        assert!(diags.iter().any(|d| d.id == "C01" && d.severity == LintSeverity::Error));
    }

    #[test]
    fn c01_does_not_fire_on_dag() {
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Proc", None, true));
        b.categories.push(cat_info("Int", None, false));
        b.categories.push(cat_info("Bool", None, false));
        b.cast_rules.push(CastRule {
            label: "IntToProc".to_string(),
            source_category: "Int".to_string(),
            target_category: "Proc".to_string(),
        });
        b.cast_rules.push(CastRule {
            label: "BoolToProc".to_string(),
            source_category: "Bool".to_string(),
            target_category: "Proc".to_string(),
        });

        let mut diags = Vec::new();
        lint_c01_cast_cycle(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }

    // ══════════════════════════════════════════════════════════════════════
    // C02: Transitive Cast Redundancy
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn c02_fires_on_redundant_direct_cast() {
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Proc", None, true));
        b.categories.push(cat_info("Int", None, false));
        b.categories.push(cat_info("Bool", None, false));
        // Int → Bool → Proc (transitive) AND Int → Proc (direct)
        b.cast_rules.push(CastRule {
            label: "IntToBool".to_string(),
            source_category: "Int".to_string(),
            target_category: "Bool".to_string(),
        });
        b.cast_rules.push(CastRule {
            label: "BoolToProc".to_string(),
            source_category: "Bool".to_string(),
            target_category: "Proc".to_string(),
        });
        b.cast_rules.push(CastRule {
            label: "IntToProc".to_string(),
            source_category: "Int".to_string(),
            target_category: "Proc".to_string(),
        });

        let mut diags = Vec::new();
        lint_c02_transitive_cast_redundancy(&b.ctx(), &mut diags);

        assert!(diags.iter().any(|d| d.id == "C02"));
    }

    #[test]
    fn c02_does_not_fire_without_indirect_path() {
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Proc", None, true));
        b.categories.push(cat_info("Int", None, false));
        b.cast_rules.push(CastRule {
            label: "IntToProc".to_string(),
            source_category: "Int".to_string(),
            target_category: "Proc".to_string(),
        });

        let mut diags = Vec::new();
        lint_c02_transitive_cast_redundancy(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }

    // ══════════════════════════════════════════════════════════════════════
    // P02: High NFA Spillover
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn p02_fires_on_many_spillover_categories() {
        let mut b = CtxBuilder::new();
        b.nfa_spillover_categories = ["A", "B", "C", "D"]
            .iter()
            .map(|s| s.to_string())
            .collect();

        let mut diags = Vec::new();
        lint_p02_high_nfa_spillover(&b.ctx(), &mut diags);

        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, "P02");
    }

    #[test]
    fn p02_does_not_fire_on_few() {
        let mut b = CtxBuilder::new();
        b.nfa_spillover_categories = ["A"].iter().map(|s| s.to_string()).collect();

        let mut diags = Vec::new();
        lint_p02_high_nfa_spillover(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }

    // ══════════════════════════════════════════════════════════════════════
    // P03: Deep Cast Nesting
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn p03_fires_on_deep_chain() {
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("A", None, true));
        b.categories.push(cat_info("B", None, false));
        b.categories.push(cat_info("C", None, false));
        b.categories.push(cat_info("D", None, false));
        b.categories.push(cat_info("E", None, false));
        // A → B → C → D → E (depth 4)
        b.cast_rules.push(CastRule {
            label: "AtoB".to_string(),
            source_category: "A".to_string(),
            target_category: "B".to_string(),
        });
        b.cast_rules.push(CastRule {
            label: "BtoC".to_string(),
            source_category: "B".to_string(),
            target_category: "C".to_string(),
        });
        b.cast_rules.push(CastRule {
            label: "CtoD".to_string(),
            source_category: "C".to_string(),
            target_category: "D".to_string(),
        });
        b.cast_rules.push(CastRule {
            label: "DtoE".to_string(),
            source_category: "D".to_string(),
            target_category: "E".to_string(),
        });

        let mut diags = Vec::new();
        lint_p03_deep_cast_nesting(&b.ctx(), &mut diags);

        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, "P03");
    }

    #[test]
    fn p03_does_not_fire_on_shallow() {
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("A", None, true));
        b.categories.push(cat_info("B", None, false));
        b.cast_rules.push(CastRule {
            label: "AtoB".to_string(),
            source_category: "A".to_string(),
            target_category: "B".to_string(),
        });

        let mut diags = Vec::new();
        lint_p03_deep_cast_nesting(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }

    // ══════════════════════════════════════════════════════════════════════
    // Display formatting
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn lint_display_format() {
        let diag = LintDiagnostic {
            id: "C01",
            name: "cast-cycle",
            severity: LintSeverity::Error,
            category: None,
            rule: None,
            message: "cast cycle detected: Int -> Proc -> Int".to_string(),
            hint: Some("break the cycle by removing one cast direction".to_string()),
            grammar_name: Some("TestGrammar".to_string()),
            source_location: None,
        };
        let s = format!("{}", diag);
        assert!(s.contains("error[C01]"));
        assert!(s.contains("cast cycle detected"));
        assert!(s.contains("= hint:"));
    }

    #[test]
    fn lint_display_no_hint() {
        let diag = LintDiagnostic {
            id: "G06",
            name: "shadowed-operator",
            severity: LintSeverity::Note,
            category: Some("Int".to_string()),
            rule: None,
            message: "operator `-` is both infix and prefix".to_string(),
            hint: None,
            grammar_name: Some("TestGrammar".to_string()),
            source_location: None,
        };
        let s = format!("{}", diag);
        assert!(s.contains("note[G06]"));
        // Display now includes a context line for category-only lints
        assert!(s.contains("= in category `Int`"));
        assert!(!s.contains("hint"));
    }

    #[test]
    fn lint_display_with_source_location() {
        let diag = LintDiagnostic {
            id: "G09",
            name: "unbalanced-delimiters",
            severity: LintSeverity::Warning,
            category: Some("Proc".to_string()),
            rule: Some("PIn".to_string()),
            message: "rule `PIn` in category `Proc` has unbalanced delimiters: 0 `(` vs 1 `)`".to_string(),
            hint: Some("add the missing `(` delimiter".to_string()),
            grammar_name: Some("RhoPi".to_string()),
            source_location: Some(crate::SourceLocation { line: 42, column: 9 }),
        };
        let s = format!("{}", diag);
        assert!(s.contains("warning[G09]"));
        assert!(s.contains("--> <macro>:42:9"));
        assert!(s.contains("= in category `Proc`, rule `PIn`"));
        assert!(s.contains("= hint:"));
    }

    #[test]
    fn lint_display_no_location_when_line_zero() {
        let diag = LintDiagnostic {
            id: "G01",
            name: "left-recursion",
            severity: LintSeverity::Warning,
            category: Some("Int".to_string()),
            rule: Some("Bad".to_string()),
            message: "left-recursive rule".to_string(),
            hint: None,
            grammar_name: Some("Test".to_string()),
            source_location: Some(crate::SourceLocation { line: 0, column: 0 }),
        };
        let s = format!("{}", diag);
        // line=0 means unknown, should not show --> line
        assert!(!s.contains("-->"));
        // But should show category/rule context
        assert!(s.contains("= in category `Int`, rule `Bad`"));
    }

    // ══════════════════════════════════════════════════════════════════════
    // char_edit_distance_is_one
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn edit_distance_one_substitution() {
        assert!(char_edit_distance_is_one("+", "*")); // single char sub
        assert!(char_edit_distance_is_one("<=", ">="));
    }

    #[test]
    fn edit_distance_one_insertion() {
        assert!(char_edit_distance_is_one("+", "++")); // insertion
        assert!(char_edit_distance_is_one("<", "<="));
    }

    #[test]
    fn edit_distance_not_one() {
        assert!(!char_edit_distance_is_one("+", "---")); // too different
        assert!(char_edit_distance_is_one("==", "!=")); // 1 sub (first char)
        assert!(!char_edit_distance_is_one("+", "+")); // zero distance
        assert!(!char_edit_distance_is_one("<<", ">>")); // 2 subs
    }

    // ── A8: Nearly-dead path W07 integration ──

    #[test]
    fn test_a8_w07_not_emitted_for_well_connected_grammar() {
        // A8: W07 should not fire for a normal 2-category grammar where both
        // categories are well-connected via bidirectional cast rules.
        let mut b = CtxBuilder::new();
        b.categories = vec![cat_info("Proc", None, true), cat_info("Int", Some("i64"), false)];
        let mut cast1 = make_rule_info("IntToProc", "Proc", vec![FirstItem::NonTerminal("Int".to_string())], false);
        cast1.is_cast = true;
        let mut cast2 = make_rule_info("ProcToInt", "Int", vec![FirstItem::NonTerminal("Proc".to_string())], false);
        cast2.is_cast = true;
        let prefix1 = make_rule_info("Par", "Proc", vec![FirstItem::Terminal("Pipe".to_string())], false);
        let prefix2 = make_rule_info("NumLit", "Int", vec![FirstItem::Terminal("Integer".to_string())], false);
        b.rules = vec![cast1, cast2, prefix1, prefix2];
        b.first_sets = [
            ("Proc".to_string(), FirstSet { tokens: ["Pipe".to_string()].into(), nullable: false }),
            ("Int".to_string(), FirstSet { tokens: ["Integer".to_string()].into(), nullable: false }),
        ].into();

        let diags = run_lints(&b.ctx());
        let w07_diags: Vec<_> = diags.iter().filter(|d| d.id == "W07").collect();
        assert!(w07_diags.is_empty(), "well-connected grammar should not emit W07: {:?}", w07_diags);
    }

    #[test]
    fn test_a8_w07_uses_note_severity() {
        // A8: NearlyDeadPath warnings must use Note severity (not Warning)
        // to distinguish from truly dead rules.
        // This test verifies the mapping at the LintDiagnostic construction level.
        let w = crate::pipeline::DeadRuleWarning::NearlyDeadPath {
            rule_label: "TestRule".to_string(),
            category: "TestCat".to_string(),
            derivation_count: 1,
            total_count: 200,
        };
        // Verify display format
        let msg = format!("{}", w);
        assert!(msg.contains("nearly-dead"));
        assert!(msg.contains("1/200"));
    }

    // ══════════════════════════════════════════════════════════════════════
    // Composition Lints (X01–X05)
    // ══════════════════════════════════════════════════════════════════════

    use crate::automata::semiring::TropicalWeight;
    use crate::prediction::DispatchAction;
    use crate::token_id::TokenIdMap;
    use crate::wfst::{PredictionWfst, WeightedAction, WeightedTransition, WfstState};

    /// Build a minimal PredictionWfst with a single start state that dispatches
    /// on the given `(token_name, rule_label, weight)` triples.
    fn make_prediction_wfst(
        category: &str,
        entries: &[(&str, &str, f64)],
    ) -> PredictionWfst {
        let mut token_map = TokenIdMap::new();
        let mut actions = Vec::new();
        let mut transitions = Vec::new();

        for &(token_name, rule_label, weight) in entries {
            let token_id = token_map.get_or_insert(token_name);
            let action_idx = actions.len() as u32;
            actions.push(WeightedAction {
                action: DispatchAction::Direct {
                    rule_label: rule_label.to_string(),
                    parse_fn: format!("parse_{}", rule_label),
                },
                weight: TropicalWeight::new(weight),
            });
            transitions.push(WeightedTransition {
                from: 0,
                input: token_id,
                action_idx,
                to: 0,
                weight: TropicalWeight::new(weight),
            });
        }

        let start_state = WfstState {
            id: 0,
            is_final: true,
            final_weight: TropicalWeight::new(0.0),
            transitions,
        };

        PredictionWfst {
            category: category.to_string(),
            states: vec![start_state],
            start: 0,
            actions,
            token_map,
            beam_width: None,
            context_labels: HashMap::new(),
        }
    }

    fn make_comp_ctx<'a>(
        first_sets_a: &'a HashMap<String, FirstSet>,
        first_sets_b: &'a HashMap<String, FirstSet>,
        first_sets_merged: &'a HashMap<String, FirstSet>,
        prediction_wfsts_a: &'a HashMap<String, PredictionWfst>,
        prediction_wfsts_b: &'a HashMap<String, PredictionWfst>,
        shared_categories: &'a [String],
        dead_rules_a: &'a HashSet<String>,
        dead_rules_b: &'a HashSet<String>,
        dead_rules_merged: &'a HashSet<String>,
        rules_a: &'a [RuleInfo],
        rules_b: &'a [RuleInfo],
        terminal_semantics_a: &'a HashMap<String, Vec<(String, String)>>,
        terminal_semantics_b: &'a HashMap<String, Vec<(String, String)>>,
    ) -> CompositionLintContext<'a> {
        CompositionLintContext {
            first_sets_a,
            first_sets_b,
            first_sets_merged,
            prediction_wfsts_a,
            prediction_wfsts_b,
            shared_categories,
            dead_rules_a,
            dead_rules_b,
            dead_rules_merged,
            rules_a,
            rules_b,
            terminal_semantics_a,
            terminal_semantics_b,
        }
    }

    // ── X01: Composition Ambiguity Introduction ──

    #[test]
    fn x01_fires_when_merged_has_new_tokens() {
        // Composition introduces a new token "Star" in the merged FIRST set
        // that was NOT present in either source grammar's FIRST set.
        // This indicates new derivation paths created by the composition.
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Expr", None, true));

        let first_a: HashMap<String, FirstSet> = [(
            "Expr".to_string(),
            FirstSet { tokens: ["Plus".to_string(), "Ident".to_string()].into(), nullable: false },
        )].into();

        let first_b: HashMap<String, FirstSet> = [(
            "Expr".to_string(),
            FirstSet { tokens: ["Minus".to_string(), "Ident".to_string()].into(), nullable: false },
        )].into();

        // Merged has "Star" which is NOT in A ∪ B = {Plus, Minus, Ident}
        let first_merged: HashMap<String, FirstSet> = [(
            "Expr".to_string(),
            FirstSet {
                tokens: ["Plus".to_string(), "Minus".to_string(), "Ident".to_string(), "Star".to_string()].into(),
                nullable: false,
            },
        )].into();

        let shared = vec!["Expr".to_string()];
        let empty_dead: HashSet<String> = HashSet::new();
        let empty_wfsts: HashMap<String, PredictionWfst> = HashMap::new();
        let empty_rules: Vec<RuleInfo> = Vec::new();
        let empty_sem: HashMap<String, Vec<(String, String)>> = HashMap::new();

        let comp_ctx = make_comp_ctx(
            &first_a, &first_b, &first_merged,
            &empty_wfsts, &empty_wfsts,
            &shared,
            &empty_dead, &empty_dead, &empty_dead,
            &empty_rules, &empty_rules,
            &empty_sem, &empty_sem,
        );

        let mut diags = Vec::new();
        lint_x01_composition_ambiguity_introduction(&b.ctx(), &comp_ctx, &mut diags);

        assert_eq!(diags.len(), 1, "expected 1 ambiguity lint for new token Star: {:?}", diags);
        assert_eq!(diags[0].id, "X01");
        assert_eq!(diags[0].severity, LintSeverity::Warning);
        assert!(diags[0].message.contains("Star"), "message should mention the new token: {}", diags[0].message);
    }

    #[test]
    fn x01_does_not_fire_when_merged_is_exact_union() {
        // Merged FIRST set is exactly A ∪ B — no new tokens introduced.
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Expr", None, true));

        let first_a: HashMap<String, FirstSet> = [(
            "Expr".to_string(),
            FirstSet { tokens: ["Plus".to_string(), "Ident".to_string()].into(), nullable: false },
        )].into();

        let first_b: HashMap<String, FirstSet> = [(
            "Expr".to_string(),
            FirstSet { tokens: ["Minus".to_string(), "Ident".to_string()].into(), nullable: false },
        )].into();

        // Merged = A ∪ B = {Plus, Minus, Ident}
        let first_merged: HashMap<String, FirstSet> = [(
            "Expr".to_string(),
            FirstSet {
                tokens: ["Plus".to_string(), "Minus".to_string(), "Ident".to_string()].into(),
                nullable: false,
            },
        )].into();

        let shared = vec!["Expr".to_string()];
        let empty_dead: HashSet<String> = HashSet::new();
        let empty_wfsts: HashMap<String, PredictionWfst> = HashMap::new();
        let empty_rules: Vec<RuleInfo> = Vec::new();
        let empty_sem: HashMap<String, Vec<(String, String)>> = HashMap::new();

        let comp_ctx = make_comp_ctx(
            &first_a, &first_b, &first_merged,
            &empty_wfsts, &empty_wfsts,
            &shared,
            &empty_dead, &empty_dead, &empty_dead,
            &empty_rules, &empty_rules,
            &empty_sem, &empty_sem,
        );

        let mut diags = Vec::new();
        lint_x01_composition_ambiguity_introduction(&b.ctx(), &comp_ctx, &mut diags);

        assert!(diags.is_empty(), "exact union should not trigger ambiguity lint: {:?}", diags);
    }

    // ── X02: Composition Priority Shadowing ──

    #[test]
    fn x02_fires_when_a_rule_shadowed_by_b() {
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Expr", None, true));

        let wfst_a: HashMap<String, PredictionWfst> = [(
            "Expr".to_string(),
            make_prediction_wfst("Expr", &[("Plus", "AddA", 0.5)]),
        )].into();

        let wfst_b: HashMap<String, PredictionWfst> = [(
            "Expr".to_string(),
            make_prediction_wfst("Expr", &[("Plus", "AddB", 0.1)]),
        )].into();

        let shared = vec!["Expr".to_string()];
        let first_a: HashMap<String, FirstSet> = [(
            "Expr".to_string(),
            FirstSet { tokens: ["Plus".to_string()].into(), nullable: false },
        )].into();
        let first_b: HashMap<String, FirstSet> = [(
            "Expr".to_string(),
            FirstSet { tokens: ["Plus".to_string()].into(), nullable: false },
        )].into();
        let first_merged: HashMap<String, FirstSet> = first_a.clone();
        let empty_dead: HashSet<String> = HashSet::new();
        let empty_rules: Vec<RuleInfo> = Vec::new();
        let empty_sem: HashMap<String, Vec<(String, String)>> = HashMap::new();

        let comp_ctx = make_comp_ctx(
            &first_a, &first_b, &first_merged,
            &wfst_a, &wfst_b,
            &shared,
            &empty_dead, &empty_dead, &empty_dead,
            &empty_rules, &empty_rules,
            &empty_sem, &empty_sem,
        );

        let mut diags = Vec::new();
        lint_x02_composition_priority_shadowing(&b.ctx(), &comp_ctx, &mut diags);

        assert_eq!(diags.len(), 1, "expected 1 shadowing lint: {:?}", diags);
        assert_eq!(diags[0].id, "X02");
        assert_eq!(diags[0].severity, LintSeverity::Warning);
        assert!(diags[0].message.contains("AddA"));
        assert!(diags[0].message.contains("AddB"));
        assert!(diags[0].message.contains("Plus"));
    }

    #[test]
    fn x02_does_not_fire_when_weights_equal() {
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Expr", None, true));

        let wfst_a: HashMap<String, PredictionWfst> = [(
            "Expr".to_string(),
            make_prediction_wfst("Expr", &[("Plus", "AddA", 0.3)]),
        )].into();

        let wfst_b: HashMap<String, PredictionWfst> = [(
            "Expr".to_string(),
            make_prediction_wfst("Expr", &[("Plus", "AddB", 0.3)]),
        )].into();

        let shared = vec!["Expr".to_string()];
        let first_a: HashMap<String, FirstSet> = [(
            "Expr".to_string(),
            FirstSet { tokens: ["Plus".to_string()].into(), nullable: false },
        )].into();
        let first_b = first_a.clone();
        let first_merged = first_a.clone();
        let empty_dead: HashSet<String> = HashSet::new();
        let empty_rules: Vec<RuleInfo> = Vec::new();
        let empty_sem: HashMap<String, Vec<(String, String)>> = HashMap::new();

        let comp_ctx = make_comp_ctx(
            &first_a, &first_b, &first_merged,
            &wfst_a, &wfst_b,
            &shared,
            &empty_dead, &empty_dead, &empty_dead,
            &empty_rules, &empty_rules,
            &empty_sem, &empty_sem,
        );

        let mut diags = Vec::new();
        lint_x02_composition_priority_shadowing(&b.ctx(), &comp_ctx, &mut diags);

        assert!(diags.is_empty(), "equal weights should not trigger shadowing: {:?}", diags);
    }

    // ── X03: Composition Dead Rule Creation ──

    #[test]
    fn x03_fires_on_newly_dead_rule() {
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Expr", None, true));

        let dead_a: HashSet<String> = HashSet::new();
        let dead_b: HashSet<String> = HashSet::new();
        let dead_merged: HashSet<String> = ["Foo".to_string()].into();

        let rules_a = vec![make_rule_info(
            "Foo", "Expr", vec![FirstItem::Terminal("+".to_string())], false,
        )];

        let empty_first: HashMap<String, FirstSet> = HashMap::new();
        let empty_wfsts: HashMap<String, PredictionWfst> = HashMap::new();
        let empty_sem: HashMap<String, Vec<(String, String)>> = HashMap::new();
        let shared = vec!["Expr".to_string()];

        let comp_ctx = make_comp_ctx(
            &empty_first, &empty_first, &empty_first,
            &empty_wfsts, &empty_wfsts,
            &shared,
            &dead_a, &dead_b, &dead_merged,
            &rules_a, &[],
            &empty_sem, &empty_sem,
        );

        let mut diags = Vec::new();
        lint_x03_composition_dead_rule_creation(&b.ctx(), &comp_ctx, &mut diags);

        assert_eq!(diags.len(), 1, "expected 1 newly-dead lint: {:?}", diags);
        assert_eq!(diags[0].id, "X03");
        assert!(diags[0].message.contains("Foo"));
        assert!(diags[0].message.contains("grammar A"));
    }

    #[test]
    fn x03_does_not_fire_for_already_dead_rules() {
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Expr", None, true));

        let dead_a: HashSet<String> = ["Bar".to_string()].into();
        let dead_b: HashSet<String> = HashSet::new();
        let dead_merged: HashSet<String> = ["Bar".to_string()].into();

        let empty_first: HashMap<String, FirstSet> = HashMap::new();
        let empty_wfsts: HashMap<String, PredictionWfst> = HashMap::new();
        let empty_sem: HashMap<String, Vec<(String, String)>> = HashMap::new();
        let shared = vec!["Expr".to_string()];
        let empty_rules: Vec<RuleInfo> = Vec::new();

        let comp_ctx = make_comp_ctx(
            &empty_first, &empty_first, &empty_first,
            &empty_wfsts, &empty_wfsts,
            &shared,
            &dead_a, &dead_b, &dead_merged,
            &empty_rules, &empty_rules,
            &empty_sem, &empty_sem,
        );

        let mut diags = Vec::new();
        lint_x03_composition_dead_rule_creation(&b.ctx(), &comp_ctx, &mut diags);

        assert!(diags.is_empty(), "already-dead rule should not trigger: {:?}", diags);
    }

    // ── X04: Composition Cast Chain Break ──

    #[test]
    fn x04_fires_when_cast_chain_broken() {
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("A", None, true));
        b.categories.push(cat_info("B", None, false));
        b.categories.push(cat_info("C", None, false));

        // Merged grammar has NO cast rules (simulating a broken chain)
        // Source A has a chain: A -> B -> C
        let rules_a = vec![
            {
                let mut r = make_rule_info(
                    "AtoB", "B", vec![FirstItem::NonTerminal("A".to_string())], false,
                );
                r.is_cast = true;
                r
            },
            {
                let mut r = make_rule_info(
                    "BtoC", "C", vec![FirstItem::NonTerminal("B".to_string())], false,
                );
                r.is_cast = true;
                r
            },
        ];

        let empty_first: HashMap<String, FirstSet> = HashMap::new();
        let empty_wfsts: HashMap<String, PredictionWfst> = HashMap::new();
        let empty_dead: HashSet<String> = HashSet::new();
        let empty_sem: HashMap<String, Vec<(String, String)>> = HashMap::new();
        let shared: Vec<String> = Vec::new();

        let comp_ctx = make_comp_ctx(
            &empty_first, &empty_first, &empty_first,
            &empty_wfsts, &empty_wfsts,
            &shared,
            &empty_dead, &empty_dead, &empty_dead,
            &rules_a, &[],
            &empty_sem, &empty_sem,
        );

        let mut diags = Vec::new();
        lint_x04_composition_cast_chain_break(&b.ctx(), &comp_ctx, &mut diags);

        // Source A has reachability: A->B, A->C (transitive), B->C
        // Merged has NO casts → reachability = {}
        // Broken: {(A,B), (A,C), (B,C)}
        assert_eq!(diags.len(), 3, "expected 3 broken cast chain lints: {:?}", diags);
        assert!(diags.iter().all(|d| d.id == "X04"));
        assert!(diags.iter().all(|d| d.severity == LintSeverity::Error));
    }

    #[test]
    fn x04_does_not_fire_when_chain_preserved() {
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("A", None, true));
        b.categories.push(cat_info("B", None, false));

        // Merged grammar preserves the cast A -> B
        b.cast_rules.push(CastRule {
            label: "AtoB".to_string(),
            source_category: "A".to_string(),
            target_category: "B".to_string(),
        });

        let rules_a = vec![{
            let mut r = make_rule_info(
                "AtoB", "B", vec![FirstItem::NonTerminal("A".to_string())], false,
            );
            r.is_cast = true;
            r
        }];

        let empty_first: HashMap<String, FirstSet> = HashMap::new();
        let empty_wfsts: HashMap<String, PredictionWfst> = HashMap::new();
        let empty_dead: HashSet<String> = HashSet::new();
        let empty_sem: HashMap<String, Vec<(String, String)>> = HashMap::new();
        let shared: Vec<String> = Vec::new();

        let comp_ctx = make_comp_ctx(
            &empty_first, &empty_first, &empty_first,
            &empty_wfsts, &empty_wfsts,
            &shared,
            &empty_dead, &empty_dead, &empty_dead,
            &rules_a, &[],
            &empty_sem, &empty_sem,
        );

        let mut diags = Vec::new();
        lint_x04_composition_cast_chain_break(&b.ctx(), &comp_ctx, &mut diags);

        assert!(diags.is_empty(), "preserved chain should not trigger: {:?}", diags);
    }

    // ── X05: Composition Terminal Collision ──

    #[test]
    fn x05_fires_on_different_semantic_roles() {
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Expr", None, true));

        let sem_a: HashMap<String, Vec<(String, String)>> = [(
            "+".to_string(),
            vec![("Int".to_string(), "infix".to_string())],
        )].into();

        let sem_b: HashMap<String, Vec<(String, String)>> = [(
            "+".to_string(),
            vec![("Str".to_string(), "prefix".to_string())],
        )].into();

        let empty_first: HashMap<String, FirstSet> = HashMap::new();
        let empty_wfsts: HashMap<String, PredictionWfst> = HashMap::new();
        let empty_dead: HashSet<String> = HashSet::new();
        let empty_rules: Vec<RuleInfo> = Vec::new();
        let shared: Vec<String> = Vec::new();

        let comp_ctx = make_comp_ctx(
            &empty_first, &empty_first, &empty_first,
            &empty_wfsts, &empty_wfsts,
            &shared,
            &empty_dead, &empty_dead, &empty_dead,
            &empty_rules, &empty_rules,
            &sem_a, &sem_b,
        );

        let mut diags = Vec::new();
        lint_x05_composition_terminal_collision(&b.ctx(), &comp_ctx, &mut diags);

        assert_eq!(diags.len(), 1, "expected 1 terminal collision lint: {:?}", diags);
        assert_eq!(diags[0].id, "X05");
        assert_eq!(diags[0].severity, LintSeverity::Warning);
        assert!(diags[0].message.contains("+"));
        assert!(diags[0].message.contains("infix"));
        assert!(diags[0].message.contains("prefix"));
    }

    #[test]
    fn x05_does_not_fire_on_same_roles() {
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Expr", None, true));

        let sem_a: HashMap<String, Vec<(String, String)>> = [(
            "+".to_string(),
            vec![("Int".to_string(), "infix".to_string())],
        )].into();

        let sem_b: HashMap<String, Vec<(String, String)>> = [(
            "+".to_string(),
            vec![("Float".to_string(), "infix".to_string())],
        )].into();

        let empty_first: HashMap<String, FirstSet> = HashMap::new();
        let empty_wfsts: HashMap<String, PredictionWfst> = HashMap::new();
        let empty_dead: HashSet<String> = HashSet::new();
        let empty_rules: Vec<RuleInfo> = Vec::new();
        let shared: Vec<String> = Vec::new();

        let comp_ctx = make_comp_ctx(
            &empty_first, &empty_first, &empty_first,
            &empty_wfsts, &empty_wfsts,
            &shared,
            &empty_dead, &empty_dead, &empty_dead,
            &empty_rules, &empty_rules,
            &sem_a, &sem_b,
        );

        let mut diags = Vec::new();
        lint_x05_composition_terminal_collision(&b.ctx(), &comp_ctx, &mut diags);

        assert!(diags.is_empty(), "same roles should not trigger collision: {:?}", diags);
    }

    // ── Integration: run_composition_lints ──

    #[test]
    fn run_composition_lints_collects_all_categories() {
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Expr", None, true));

        // Set up data that triggers X02 (shadowing) and X05 (collision)
        let wfst_a: HashMap<String, PredictionWfst> = [(
            "Expr".to_string(),
            make_prediction_wfst("Expr", &[("Plus", "AddA", 0.8)]),
        )].into();
        let wfst_b: HashMap<String, PredictionWfst> = [(
            "Expr".to_string(),
            make_prediction_wfst("Expr", &[("Plus", "AddB", 0.1)]),
        )].into();

        let shared = vec!["Expr".to_string()];
        let first_a: HashMap<String, FirstSet> = [(
            "Expr".to_string(),
            FirstSet { tokens: ["Plus".to_string()].into(), nullable: false },
        )].into();
        let first_b = first_a.clone();
        let first_merged = first_a.clone();

        let sem_a: HashMap<String, Vec<(String, String)>> = [(
            "*".to_string(),
            vec![("Int".to_string(), "infix".to_string())],
        )].into();
        let sem_b: HashMap<String, Vec<(String, String)>> = [(
            "*".to_string(),
            vec![("Str".to_string(), "repeat".to_string())],
        )].into();

        let dead_merged: HashSet<String> = ["Orphan".to_string()].into();
        let rules_a = vec![make_rule_info(
            "Orphan", "Expr", vec![FirstItem::Terminal("~".to_string())], false,
        )];
        let empty_dead: HashSet<String> = HashSet::new();

        let comp_ctx = make_comp_ctx(
            &first_a, &first_b, &first_merged,
            &wfst_a, &wfst_b,
            &shared,
            &empty_dead, &empty_dead, &dead_merged,
            &rules_a, &[],
            &sem_a, &sem_b,
        );

        let diags = run_composition_lints(&b.ctx(), &comp_ctx);

        // Should have at least X02 (shadowing on Plus) and X05 (collision on *)
        // and X03 (Orphan newly dead)
        let x02_count = diags.iter().filter(|d| d.id == "X02").count();
        let x03_count = diags.iter().filter(|d| d.id == "X03").count();
        let x05_count = diags.iter().filter(|d| d.id == "X05").count();

        assert!(x02_count >= 1, "expected X02 shadowing lint: {:?}", diags);
        assert_eq!(x03_count, 1, "expected 1 X03 dead-rule lint: {:?}", diags);
        assert_eq!(x05_count, 1, "expected 1 X05 collision lint: {:?}", diags);
    }

    // ── G24: Alpha-Equivalent Rules ──

    #[test]
    fn test_g24_variable_renamed_rules_deferred_to_g07() {
        // Two rules with different variable names but identical structure:
        //   AddA: x "+" y   (uses vars x, y)
        //   AddB: a "+" b   (uses vars a, b)
        // G07's syntax_signature drops param_names, so these have identical
        // signatures → G07 catches them. G24 should NOT double-report.
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Expr", None, true));
        b.all_syntax.push((
            "AddA".to_string(),
            "Expr".to_string(),
            vec![
                SyntaxItemSpec::NonTerminal { category: "Expr".to_string(), param_name: "x".to_string() },
                SyntaxItemSpec::Terminal("+".to_string()),
                SyntaxItemSpec::NonTerminal { category: "Expr".to_string(), param_name: "y".to_string() },
            ],
        ));
        b.all_syntax.push((
            "AddB".to_string(),
            "Expr".to_string(),
            vec![
                SyntaxItemSpec::NonTerminal { category: "Expr".to_string(), param_name: "a".to_string() },
                SyntaxItemSpec::Terminal("+".to_string()),
                SyntaxItemSpec::NonTerminal { category: "Expr".to_string(), param_name: "b".to_string() },
            ],
        ));
        let mut diagnostics = Vec::new();
        lint_g24_alpha_equivalent_rules(&b.ctx(), &mut diagnostics);
        assert!(diagnostics.is_empty(), "G07 covers these; G24 should not double-report");
    }

    #[test]
    fn test_g24_g07_false_positive_different_binding_structure() {
        // G07 incorrectly groups these because it drops param_names:
        //   SelfEq: x "==" x   (same variable used twice — requires both sides identical)
        //   AnyEq:  a "==" b   (different variables — accepts any two sides)
        // G07 signature for both: NT(Expr)|T(==)|NT(Expr) → groups them as "identical"
        // G24 De Bruijn encoding distinguishes them:
        //   SelfEq: [NewVar, ..., VarRef(0), ...]
        //   AnyEq:  [NewVar, ..., NewVar, ...]
        // So G24 should NOT report these as α-equivalent (they genuinely differ).
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Expr", None, true));
        b.all_syntax.push((
            "SelfEq".to_string(),
            "Expr".to_string(),
            vec![
                SyntaxItemSpec::NonTerminal { category: "Expr".to_string(), param_name: "x".to_string() },
                SyntaxItemSpec::Terminal("==".to_string()),
                SyntaxItemSpec::NonTerminal { category: "Expr".to_string(), param_name: "x".to_string() },
            ],
        ));
        b.all_syntax.push((
            "AnyEq".to_string(),
            "Expr".to_string(),
            vec![
                SyntaxItemSpec::NonTerminal { category: "Expr".to_string(), param_name: "a".to_string() },
                SyntaxItemSpec::Terminal("==".to_string()),
                SyntaxItemSpec::NonTerminal { category: "Expr".to_string(), param_name: "b".to_string() },
            ],
        ));
        let mut diagnostics = Vec::new();
        lint_g24_alpha_equivalent_rules(&b.ctx(), &mut diagnostics);
        assert!(
            diagnostics.is_empty(),
            "SelfEq and AnyEq have different binding structure; G24 should not group them"
        );
    }

    #[test]
    fn test_g24_structurally_different_rules_not_flagged() {
        // Two rules with different structure — G24 should NOT fire.
        //   Add: x "+" y     (binary infix)
        //   Neg: "-" x       (unary prefix)
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Expr", None, true));
        b.all_syntax.push((
            "Add".to_string(),
            "Expr".to_string(),
            vec![
                SyntaxItemSpec::NonTerminal { category: "Expr".to_string(), param_name: "x".to_string() },
                SyntaxItemSpec::Terminal("+".to_string()),
                SyntaxItemSpec::NonTerminal { category: "Expr".to_string(), param_name: "y".to_string() },
            ],
        ));
        b.all_syntax.push((
            "Neg".to_string(),
            "Expr".to_string(),
            vec![
                SyntaxItemSpec::Terminal("-".to_string()),
                SyntaxItemSpec::NonTerminal { category: "Expr".to_string(), param_name: "x".to_string() },
            ],
        ));
        let mut diagnostics = Vec::new();
        lint_g24_alpha_equivalent_rules(&b.ctx(), &mut diagnostics);
        assert!(diagnostics.is_empty(), "no G24 for structurally different rules");
    }

    #[test]
    fn test_g24_same_vars_different_structure_not_flagged() {
        // Two rules with same variable names but different structure — G24 should NOT fire.
        //   Pair: x "," y
        //   Add:  x "+" y
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Expr", None, true));
        b.all_syntax.push((
            "Pair".to_string(),
            "Expr".to_string(),
            vec![
                SyntaxItemSpec::NonTerminal { category: "Expr".to_string(), param_name: "x".to_string() },
                SyntaxItemSpec::Terminal(",".to_string()),
                SyntaxItemSpec::NonTerminal { category: "Expr".to_string(), param_name: "y".to_string() },
            ],
        ));
        b.all_syntax.push((
            "Add".to_string(),
            "Expr".to_string(),
            vec![
                SyntaxItemSpec::NonTerminal { category: "Expr".to_string(), param_name: "x".to_string() },
                SyntaxItemSpec::Terminal("+".to_string()),
                SyntaxItemSpec::NonTerminal { category: "Expr".to_string(), param_name: "y".to_string() },
            ],
        ));
        let mut diagnostics = Vec::new();
        lint_g24_alpha_equivalent_rules(&b.ctx(), &mut diagnostics);
        assert!(diagnostics.is_empty(), "no G24 for rules with different terminals");
    }

    #[test]
    fn test_g24_exact_duplicates_deferred_to_g07() {
        // Two rules with IDENTICAL syntax (including variable names) — G07 territory.
        // G24 should NOT fire because sigs.len() == 1 (exact match).
        let mut b = CtxBuilder::new();
        b.categories.push(cat_info("Expr", None, true));
        let syntax = vec![
            SyntaxItemSpec::NonTerminal { category: "Expr".to_string(), param_name: "x".to_string() },
            SyntaxItemSpec::Terminal("+".to_string()),
            SyntaxItemSpec::NonTerminal { category: "Expr".to_string(), param_name: "y".to_string() },
        ];
        b.all_syntax.push(("Add1".to_string(), "Expr".to_string(), syntax.clone()));
        b.all_syntax.push(("Add2".to_string(), "Expr".to_string(), syntax));
        let mut diagnostics = Vec::new();
        lint_g24_alpha_equivalent_rules(&b.ctx(), &mut diagnostics);
        assert!(diagnostics.is_empty(), "exact duplicates should be left to G07, not G24");
    }

    #[test]
    fn test_debruijn_encoding_alpha_equivalence() {
        // Direct test of the De Bruijn encoding: α-equivalent syntax items
        // must produce identical byte sequences.
        let syntax_a = vec![
            SyntaxItemSpec::NonTerminal { category: "Expr".to_string(), param_name: "x".to_string() },
            SyntaxItemSpec::Terminal("+".to_string()),
            SyntaxItemSpec::NonTerminal { category: "Expr".to_string(), param_name: "y".to_string() },
        ];
        let syntax_b = vec![
            SyntaxItemSpec::NonTerminal { category: "Expr".to_string(), param_name: "a".to_string() },
            SyntaxItemSpec::Terminal("+".to_string()),
            SyntaxItemSpec::NonTerminal { category: "Expr".to_string(), param_name: "b".to_string() },
        ];
        assert_eq!(
            syntax_item_debruijn_bytes(&syntax_a),
            syntax_item_debruijn_bytes(&syntax_b),
            "α-equivalent syntax must produce identical De Bruijn bytes"
        );
    }

    #[test]
    fn test_debruijn_encoding_different_structure() {
        // Structurally different syntax items must produce DIFFERENT byte sequences.
        let syntax_a = vec![
            SyntaxItemSpec::NonTerminal { category: "Expr".to_string(), param_name: "x".to_string() },
            SyntaxItemSpec::Terminal("+".to_string()),
            SyntaxItemSpec::NonTerminal { category: "Expr".to_string(), param_name: "y".to_string() },
        ];
        let syntax_b = vec![
            SyntaxItemSpec::Terminal("-".to_string()),
            SyntaxItemSpec::NonTerminal { category: "Expr".to_string(), param_name: "x".to_string() },
        ];
        assert_ne!(
            syntax_item_debruijn_bytes(&syntax_a),
            syntax_item_debruijn_bytes(&syntax_b),
            "structurally different syntax must produce different De Bruijn bytes"
        );
    }

    #[test]
    fn test_debruijn_var_reuse_same_slot() {
        // When the same variable appears twice, both references should use the same slot.
        // x "?" x   vs   a "?" a   should be identical
        let syntax_a = vec![
            SyntaxItemSpec::NonTerminal { category: "Expr".to_string(), param_name: "x".to_string() },
            SyntaxItemSpec::Terminal("?".to_string()),
            SyntaxItemSpec::NonTerminal { category: "Expr".to_string(), param_name: "x".to_string() },
        ];
        let syntax_b = vec![
            SyntaxItemSpec::NonTerminal { category: "Expr".to_string(), param_name: "a".to_string() },
            SyntaxItemSpec::Terminal("?".to_string()),
            SyntaxItemSpec::NonTerminal { category: "Expr".to_string(), param_name: "a".to_string() },
        ];
        let bytes_a = syntax_item_debruijn_bytes(&syntax_a);
        let bytes_b = syntax_item_debruijn_bytes(&syntax_b);
        assert_eq!(bytes_a, bytes_b, "same-var-reuse must produce identical bytes");

        // x "?" y  should differ from  x "?" x  (different binding structure)
        let syntax_c = vec![
            SyntaxItemSpec::NonTerminal { category: "Expr".to_string(), param_name: "x".to_string() },
            SyntaxItemSpec::Terminal("?".to_string()),
            SyntaxItemSpec::NonTerminal { category: "Expr".to_string(), param_name: "y".to_string() },
        ];
        assert_ne!(
            bytes_a,
            syntax_item_debruijn_bytes(&syntax_c),
            "different binding structure must produce different bytes"
        );
    }

    // ══════════════════════════════════════════════════════════════════════
    // Info severity and format_diagnostic_colored tests
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn info_severity_display() {
        assert_eq!(format!("{}", LintSeverity::Info), "info");
    }

    #[test]
    fn info_severity_ord() {
        assert!(LintSeverity::Info < LintSeverity::Note);
        assert!(LintSeverity::Note < LintSeverity::Warning);
        assert!(LintSeverity::Warning < LintSeverity::Error);
    }

    #[test]
    fn format_diagnostic_colored_info_with_grammar_name() {
        let diag = LintDiagnostic {
            id: "I01",
            name: "transducer-cascade",
            severity: LintSeverity::Info,
            category: None,
            rule: None,
            message: "transducer cascade: 8 change(s) across 3 categories".to_string(),
            hint: None,
            grammar_name: Some("Ambient".to_string()),
            source_location: None,
        };
        let output = format_diagnostic_colored(&diag);
        // Should contain the severity, lint code, grammar name, and message
        assert!(output.contains("info"), "should contain 'info' severity");
        assert!(output.contains("I01"), "should contain lint code I01");
        assert!(output.contains("(Ambient)"), "should contain grammar name in parens");
        assert!(output.contains("transducer cascade"), "should contain message");
    }

    #[test]
    fn format_diagnostic_colored_no_grammar_name() {
        let diag = LintDiagnostic {
            id: "I08",
            name: "env-override-active",
            severity: LintSeverity::Warning,
            category: None,
            rule: None,
            message: "PRATTAIL_AUTO_OPTIMIZE override active".to_string(),
            hint: Some("unset PRATTAIL_AUTO_OPTIMIZE".to_string()),
            grammar_name: None,
            source_location: None,
        };
        let output = format_diagnostic_colored(&diag);
        // Should NOT contain grammar name parens
        assert!(!output.contains("()"), "should not contain empty parens");
        assert!(output.contains("warning"), "should contain 'warning' severity");
        assert!(output.contains("I08"), "should contain lint code I08");
        assert!(output.contains("hint:"), "should contain hint");
    }

    #[test]
    fn format_diagnostic_colored_info_with_hint() {
        let diag = LintDiagnostic {
            id: "I04",
            name: "beam-feature-required",
            severity: LintSeverity::Warning,
            category: None,
            rule: None,
            message: "beam_width: auto requires `wfst-log`".to_string(),
            hint: Some("enable `wfst-log` feature or use explicit beam_width".to_string()),
            grammar_name: Some("TestGrammar".to_string()),
            source_location: None,
        };
        let output = format_diagnostic_colored(&diag);
        assert!(output.contains("I04"), "should contain lint code");
        assert!(output.contains("(TestGrammar)"), "should contain grammar name");
        assert!(output.contains("hint:"), "should contain hint line");
        assert!(output.contains("wfst-log"), "hint should mention wfst-log");
    }

    // ══════════════════════════════════════════════════════════════════════
    // Diagnostic Grouping Tests
    // ══════════════════════════════════════════════════════════════════════

    fn make_diag(
        id: &'static str,
        name: &'static str,
        severity: LintSeverity,
        category: Option<&str>,
        rule: Option<&str>,
        message: &str,
        hint: Option<&str>,
    ) -> LintDiagnostic {
        LintDiagnostic {
            id,
            name,
            severity,
            category: category.map(|s| s.to_string()),
            rule: rule.map(|s| s.to_string()),
            message: message.to_string(),
            hint: hint.map(|s| s.to_string()),
            grammar_name: Some("TestGrammar".to_string()),
            source_location: None,
        }
    }

    #[test]
    fn group_empty_input() {
        let result = group_diagnostics(Vec::new());
        assert!(result.is_empty());
    }

    #[test]
    fn group_w01_single_passes_through() {
        let diag = make_diag(
            "W01", "dead-rule", LintSeverity::Warning,
            Some("Int"), Some("FloatToStr"),
            "rule `FloatToStr` in category `Int` is unreachable",
            Some("remove the rule or add a unique dispatch token"),
        );
        let result = group_diagnostics(vec![diag.clone()]);
        assert_eq!(result.len(), 1);
        assert_eq!(result[0].id, "W01");
        assert_eq!(result[0].category.as_deref(), Some("Int"));
    }

    #[test]
    fn group_w01_multiple_same_type() {
        let hint = "remove the rule or add a unique dispatch token";
        let diags = vec![
            make_diag("W01", "dead-rule", LintSeverity::Warning, Some("Str"), Some("FloatToStr"), "rule `FloatToStr` unreachable", Some(hint)),
            make_diag("W01", "dead-rule", LintSeverity::Warning, Some("Str"), Some("BoolToStr"), "rule `BoolToStr` unreachable", Some(hint)),
            make_diag("W01", "dead-rule", LintSeverity::Warning, Some("Bool"), Some("IntToBool"), "rule `IntToBool` unreachable", Some(hint)),
            make_diag("W01", "dead-rule", LintSeverity::Warning, Some("Int"), Some("FloatToInt"), "rule `FloatToInt` unreachable", Some(hint)),
            make_diag("W01", "dead-rule", LintSeverity::Warning, Some("Int"), Some("StrToInt"), "rule `StrToInt` unreachable", Some(hint)),
        ];
        let result = group_diagnostics(diags);
        assert_eq!(result.len(), 1, "5 W01 with same hint should become 1 grouped diagnostic");
        assert_eq!(result[0].id, "W01");
        assert!(result[0].message.contains("5 rules are unreachable"), "message: {}", result[0].message);
        assert!(result[0].message.contains("Str: FloatToStr, BoolToStr"), "should list Str rules: {}", result[0].message);
        assert!(result[0].message.contains("Bool: IntToBool"), "should list Bool rules: {}", result[0].message);
        assert!(result[0].message.contains("Int: FloatToInt, StrToInt"), "should list Int rules: {}", result[0].message);
        assert!(result[0].category.is_none(), "grouped diagnostic has no single category");
    }

    #[test]
    fn group_w01_mixed_types_separate() {
        let diags = vec![
            make_diag("W01", "dead-rule", LintSeverity::Warning, Some("Str"), Some("FloatToStr"), "rule unreachable", Some("hint A")),
            make_diag("W01", "dead-rule", LintSeverity::Warning, Some("Str"), Some("BoolToStr"), "rule unreachable", Some("hint A")),
            make_diag("W01", "dead-rule", LintSeverity::Warning, Some("Int"), Some("BadRule"), "rule unreachable", Some("hint B")),
        ];
        let result = group_diagnostics(diags);
        // Two different hints → two groups (one grouped, one pass-through)
        assert_eq!(result.len(), 2, "different hints produce separate groups");
        assert_eq!(result[0].id, "W01");
        assert_eq!(result[1].id, "W01");
    }

    #[test]
    fn group_g03_multiple_categories() {
        let diags = vec![
            make_diag("G03", "ambiguous-prefix", LintSeverity::Warning, Some("Int"), None, "ambiguous prefix for token `kw` in Int", Some("add unique dispatch tokens")),
            make_diag("G03", "ambiguous-prefix", LintSeverity::Warning, Some("Float"), None, "ambiguous prefix for token `kw` in Float", Some("add unique dispatch tokens")),
        ];
        let result = group_diagnostics(diags);
        assert_eq!(result.len(), 1);
        assert_eq!(result[0].id, "G03");
        assert!(result[0].message.contains("2 ambiguous prefix dispatch"), "message: {}", result[0].message);
        assert!(result[0].message.contains("2 categories"), "message: {}", result[0].message);
    }

    #[test]
    fn group_g08_all_merged() {
        let diags = vec![
            make_diag("G08", "missing-cast-to-root", LintSeverity::Warning, Some("Float"), None, "no cast path from category `Float` to primary category `Proc`", Some("add a cast rule")),
            make_diag("G08", "missing-cast-to-root", LintSeverity::Warning, Some("Bool"), None, "no cast path from category `Bool` to primary category `Proc`", Some("add a cast rule")),
            make_diag("G08", "missing-cast-to-root", LintSeverity::Warning, Some("Str"), None, "no cast path from category `Str` to primary category `Proc`", Some("add a cast rule")),
        ];
        let result = group_diagnostics(diags);
        assert_eq!(result.len(), 1);
        assert_eq!(result[0].id, "G08");
        assert!(result[0].message.contains("3 categories have no cast path"), "message: {}", result[0].message);
        assert!(result[0].message.contains("isolated: Float, Bool, Str"), "message: {}", result[0].message);
    }

    #[test]
    fn group_preserves_non_grouped_ids() {
        let diags = vec![
            make_diag("G01", "left-recursion", LintSeverity::Warning, Some("Int"), Some("Bad"), "left recursive", None),
            make_diag("C01", "cast-cycle", LintSeverity::Error, None, None, "cycle detected", None),
        ];
        let result = group_diagnostics(diags);
        assert_eq!(result.len(), 2);
        assert_eq!(result[0].id, "G01");
        assert_eq!(result[1].id, "C01");
    }

    #[test]
    fn group_mixed_ids_preserves_order() {
        let diags = vec![
            make_diag("G01", "left-recursion", LintSeverity::Warning, Some("Int"), None, "left recursive", None),
            make_diag("W01", "dead-rule", LintSeverity::Warning, Some("Str"), Some("R1"), "dead", Some("hint")),
            make_diag("C01", "cast-cycle", LintSeverity::Error, None, None, "cycle", None),
            make_diag("W01", "dead-rule", LintSeverity::Warning, Some("Str"), Some("R2"), "dead", Some("hint")),
        ];
        let result = group_diagnostics(diags);
        // G01 at index 0, W01 grouped at index 1 (first occurrence position), C01 at index 2
        assert_eq!(result.len(), 3);
        assert_eq!(result[0].id, "G01");
        assert_eq!(result[1].id, "W01");
        assert!(result[1].message.contains("2 rules are unreachable"), "W01 should be grouped");
        assert_eq!(result[2].id, "C01");
    }

    #[test]
    fn group_g27_by_general_rule() {
        let diags = vec![
            make_diag("G27", "rule-subsumption-candidate", LintSeverity::Warning, None, None, "rule `AmbNew` may be subsumed by more general rule `AmbCong`", Some("review")),
            make_diag("G27", "rule-subsumption-candidate", LintSeverity::Warning, None, None, "rule `OutRule` may be subsumed by more general rule `AmbCong`", Some("review")),
            make_diag("G27", "rule-subsumption-candidate", LintSeverity::Warning, None, None, "rule `FooRule` may be subsumed by more general rule `AmbCong`", Some("review")),
        ];
        let result = group_diagnostics(diags);
        assert_eq!(result.len(), 1);
        assert_eq!(result[0].id, "G27");
        assert!(result[0].message.contains("3 rules may be subsumed"), "message: {}", result[0].message);
        assert!(result[0].message.contains("candidates: AmbNew, OutRule, FooRule"), "message: {}", result[0].message);
    }

    #[test]
    fn group_g27_different_generals() {
        let diags = vec![
            make_diag("G27", "rule-subsumption-candidate", LintSeverity::Warning, None, None, "rule `A` may be subsumed by more general rule `Gen1`", Some("review")),
            make_diag("G27", "rule-subsumption-candidate", LintSeverity::Warning, None, None, "rule `B` may be subsumed by more general rule `Gen2`", Some("review")),
        ];
        let result = group_diagnostics(diags);
        // Two different general rules → each passes through individually (single-item groups)
        assert_eq!(result.len(), 2);
        assert_eq!(result[0].id, "G27");
        assert_eq!(result[1].id, "G27");
    }

    #[test]
    fn group_w05_by_category() {
        let diags: Vec<LintDiagnostic> = (0..5)
            .map(|i| make_diag(
                "W05", "composed-dispatch-ambiguity", LintSeverity::Warning,
                Some("Float"), None,
                &format!(
                    "2-way ambiguity at DFA state {}: 2 derivations\n\
                     \x20 - Token::KwFn → rule FnFloat (weight 1.00)\n\
                     \x20 - Token::KwFn → rule Ident (weight 11.00)\n\
                     \x20 Resolved by tropical shortest path → FnFloat",
                    i
                ),
                Some("assign distinct WFST weights to disambiguate"),
            ))
            .chain((0..3).map(|i| make_diag(
                "W05", "composed-dispatch-ambiguity", LintSeverity::Warning,
                Some("Int"), None,
                &format!(
                    "2-way ambiguity at DFA state {}: 2 derivations\n\
                     \x20 - Token::KwInt → rule IntCast (weight 1.00)\n\
                     \x20 - Token::KwInt → rule Ident (weight 11.00)\n\
                     \x20 Resolved by tropical shortest path → IntCast",
                    i + 10
                ),
                Some("assign distinct WFST weights to disambiguate"),
            )))
            .collect();
        let result = group_diagnostics(diags);
        assert_eq!(result.len(), 1, "8 W05 should become 1 grouped: {:#?}", result.iter().map(|d| &d.message).collect::<Vec<_>>());
        assert_eq!(result[0].id, "W05");
        assert!(result[0].message.contains("8 ambiguities resolved"), "message: {}", result[0].message);
        assert!(result[0].message.contains("Float:"), "should list Float: {}", result[0].message);
        assert!(result[0].message.contains("Int:"), "should list Int: {}", result[0].message);
    }

    #[test]
    fn group_w05_single_passes_through() {
        let diag = make_diag(
            "W05", "composed-dispatch-ambiguity", LintSeverity::Warning,
            Some("Float"), None, "2-way ambiguity at DFA state 0", Some("hint"),
        );
        let result = group_diagnostics(vec![diag]);
        assert_eq!(result.len(), 1);
        assert_eq!(result[0].category.as_deref(), Some("Float"));
    }

    #[test]
    fn group_w07_multiple() {
        let diags = vec![
            make_diag("W07", "nearly-dead-path", LintSeverity::Note, Some("Str"), Some("R1"), "nearly dead", Some("hint")),
            make_diag("W07", "nearly-dead-path", LintSeverity::Note, Some("Str"), Some("R2"), "nearly dead", Some("hint")),
            make_diag("W07", "nearly-dead-path", LintSeverity::Note, Some("Bool"), Some("R3"), "nearly dead", Some("hint")),
        ];
        let result = group_diagnostics(diags);
        assert_eq!(result.len(), 1);
        assert_eq!(result[0].id, "W07");
        assert!(result[0].message.contains("3 rules on nearly-dead paths"), "message: {}", result[0].message);
        assert!(result[0].message.contains("Bool: R3"), "message: {}", result[0].message);
        assert!(result[0].message.contains("Str: R1, R2"), "message: {}", result[0].message);
    }

    // ══════════════════════════════════════════════════════════════════════
    // S01: Safety Violation
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn s01_fires_on_unsafe() {
        let mut b = CtxBuilder::new();
        b.safety_result_data = Some(crate::verify::SafetyResult {
            safe: false,
            initial_weight: crate::automata::semiring::BooleanWeight(true),
            witness_trace: vec![],
        });
        let mut diags = Vec::new();
        lint_s01_safety_violation(&b.ctx(), &mut diags);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, "S01");
        assert_eq!(diags[0].severity, LintSeverity::Warning);
    }

    #[test]
    fn s01_silent_when_safe() {
        let mut b = CtxBuilder::new();
        b.safety_result_data = Some(crate::verify::SafetyResult {
            safe: true,
            initial_weight: crate::automata::semiring::BooleanWeight(true),
            witness_trace: vec![],
        });
        let mut diags = Vec::new();
        lint_s01_safety_violation(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }

    // ══════════════════════════════════════════════════════════════════════
    // S02: Safety Verified
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn s02_fires_when_safe() {
        let mut b = CtxBuilder::new();
        b.safety_result_data = Some(crate::verify::SafetyResult {
            safe: true,
            initial_weight: crate::automata::semiring::BooleanWeight(true),
            witness_trace: vec![],
        });
        let mut diags = Vec::new();
        lint_s02_safety_verified(&b.ctx(), &mut diags);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, "S02");
        assert_eq!(diags[0].severity, LintSeverity::Note);
    }

    #[test]
    fn s02_silent_when_unsafe() {
        let mut b = CtxBuilder::new();
        b.safety_result_data = Some(crate::verify::SafetyResult {
            safe: false,
            initial_weight: crate::automata::semiring::BooleanWeight(true),
            witness_trace: vec![],
        });
        let mut diags = Vec::new();
        lint_s02_safety_verified(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }

    // ══════════════════════════════════════════════════════════════════════
    // S03: CEGAR Refinement
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn s03_fires_with_cegar_log() {
        let mut b = CtxBuilder::new();
        b.cegar_result_data = Some(crate::cegar::CegarLog {
            steps: vec![crate::cegar::RefinementStep {
                level: crate::cegar::AbstractionLevel::Boolean,
                verdict: crate::verify::Verdict::Verified,
                counterexample: None,
                is_spurious: false,
                refinement_action: "none".to_string(),
            }],
        });
        let mut diags = Vec::new();
        lint_s03_cegar_refinement(&b.ctx(), &mut diags);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, "S03");
        assert_eq!(diags[0].severity, LintSeverity::Note);
    }

    #[test]
    fn s03_silent_when_none() {
        let b = CtxBuilder::new();
        let mut diags = Vec::new();
        lint_s03_cegar_refinement(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }

    // ══════════════════════════════════════════════════════════════════════
    // S06: Algebraic Summary
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn s06_fires_with_summary() {
        let mut b = CtxBuilder::new();
        b.algebraic_result_data = Some(crate::algebraic::AlgebraicSummary {
            scc_count: 3,
            path_expression_count: 2,
            scc_summaries: vec!["SCC0".to_string()],
        });
        let mut diags = Vec::new();
        lint_s06_algebraic_summary(&b.ctx(), &mut diags);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, "S06");
        assert_eq!(diags[0].severity, LintSeverity::Note);
    }

    #[test]
    fn s06_silent_when_none() {
        let b = CtxBuilder::new();
        let mut diags = Vec::new();
        lint_s06_algebraic_summary(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }

    // ══════════════════════════════════════════════════════════════════════
    // P06: Analysis Pipeline Cost
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn p06_fires_on_meaningful_elapsed() {
        let mut b = CtxBuilder::new();
        b.math_analysis_elapsed_data = Some(std::time::Duration::from_millis(5));
        let mut diags = Vec::new();
        lint_p06_analysis_pipeline_cost(&b.ctx(), &mut diags);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, "P06");
        assert_eq!(diags[0].severity, LintSeverity::Note);
    }

    #[test]
    fn p06_silent_on_trivial_elapsed() {
        let mut b = CtxBuilder::new();
        b.math_analysis_elapsed_data = Some(std::time::Duration::from_micros(10));
        let mut diags = Vec::new();
        lint_p06_analysis_pipeline_cost(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }

    // ══════════════════════════════════════════════════════════════════════
    // T01-T04: TRS Analysis (feature = "trs-analysis")
    // ══════════════════════════════════════════════════════════════════════

    #[cfg(feature = "trs-analysis")]
    #[test]
    fn t01_fires_on_non_joinable() {
        use crate::confluence::{ConfluenceAnalysis, CriticalPair, JoinabilityResult, Term};
        let mut b = CtxBuilder::new();
        b.confluence_result_data = Some(ConfluenceAnalysis {
            is_confluent: false,
            critical_pairs: vec![CriticalPair {
                term1: Term::var("x"),
                term2: Term::var("y"),
                rule1_index: 0,
                rule2_index: 1,
                overlap_position: vec![0],
            }],
            joinability_results: vec![JoinabilityResult::NotJoinable {
                normal_form1: Term::var("x"),
                normal_form2: Term::var("y"),
            }],
            non_joinable_count: 1,
            unknown_count: 0,
        });
        let mut diags = Vec::new();
        lint_t01_non_joinable_critical_pair(&b.ctx(), &mut diags);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, "T01");
        assert_eq!(diags[0].severity, LintSeverity::Warning);
    }

    #[cfg(feature = "trs-analysis")]
    #[test]
    fn t01_silent_when_none() {
        let b = CtxBuilder::new();
        let mut diags = Vec::new();
        lint_t01_non_joinable_critical_pair(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }

    #[cfg(feature = "trs-analysis")]
    #[test]
    fn t02_fires_when_confluent() {
        use crate::confluence::ConfluenceAnalysis;
        let mut b = CtxBuilder::new();
        b.confluence_result_data = Some(ConfluenceAnalysis {
            is_confluent: true,
            critical_pairs: vec![],
            joinability_results: vec![],
            non_joinable_count: 0,
            unknown_count: 0,
        });
        let mut diags = Vec::new();
        lint_t02_confluence_verified(&b.ctx(), &mut diags);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, "T02");
        assert_eq!(diags[0].severity, LintSeverity::Note);
    }

    #[cfg(feature = "trs-analysis")]
    #[test]
    fn t02_silent_when_not_confluent() {
        use crate::confluence::ConfluenceAnalysis;
        let mut b = CtxBuilder::new();
        b.confluence_result_data = Some(ConfluenceAnalysis {
            is_confluent: false,
            critical_pairs: vec![],
            joinability_results: vec![],
            non_joinable_count: 0,
            unknown_count: 0,
        });
        let mut diags = Vec::new();
        lint_t02_confluence_verified(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }

    #[cfg(feature = "trs-analysis")]
    #[test]
    fn t03_fires_on_non_terminating() {
        use crate::termination::TerminationResult;
        let mut b = CtxBuilder::new();
        b.termination_result_data = Some(TerminationResult::PotentiallyNonTerminating {
            reason: "cycle in SCC".to_string(),
            problematic_sccs: vec![0],
        });
        let mut diags = Vec::new();
        lint_t03_non_terminating_cycle(&b.ctx(), &mut diags);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, "T03");
        assert_eq!(diags[0].severity, LintSeverity::Warning);
    }

    #[cfg(feature = "trs-analysis")]
    #[test]
    fn t03_silent_when_terminating() {
        use crate::termination::TerminationResult;
        let mut b = CtxBuilder::new();
        b.termination_result_data = Some(TerminationResult::Terminating);
        let mut diags = Vec::new();
        lint_t03_non_terminating_cycle(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }

    #[cfg(feature = "trs-analysis")]
    #[test]
    fn t04_fires_when_terminating() {
        use crate::termination::TerminationResult;
        let mut b = CtxBuilder::new();
        b.termination_result_data = Some(TerminationResult::Terminating);
        let mut diags = Vec::new();
        lint_t04_termination_verified(&b.ctx(), &mut diags);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, "T04");
        assert_eq!(diags[0].severity, LintSeverity::Note);
    }

    #[cfg(feature = "trs-analysis")]
    #[test]
    fn t04_silent_when_not_terminating() {
        use crate::termination::TerminationResult;
        let mut b = CtxBuilder::new();
        b.termination_result_data = Some(TerminationResult::PotentiallyNonTerminating {
            reason: "cycle".to_string(),
            problematic_sccs: vec![0],
        });
        let mut diags = Vec::new();
        lint_t04_termination_verified(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }

    // ══════════════════════════════════════════════════════════════════════
    // V01-V02: VPA (feature = "vpa")
    // ══════════════════════════════════════════════════════════════════════

    #[cfg(feature = "vpa")]
    #[test]
    fn v01_fires_when_determinizable() {
        let mut b = CtxBuilder::new();
        b.vpa_result_data = Some(crate::vpa::VpaAnalysis {
            is_determinizable: true,
            alphabet_mismatches: vec![],
            state_count: 5,
        });
        let mut diags = Vec::new();
        lint_v01_vpa_determinizable(&b.ctx(), &mut diags);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, "V01");
        assert_eq!(diags[0].severity, LintSeverity::Note);
    }

    #[cfg(feature = "vpa")]
    #[test]
    fn v01_silent_when_not_determinizable() {
        let mut b = CtxBuilder::new();
        b.vpa_result_data = Some(crate::vpa::VpaAnalysis {
            is_determinizable: false,
            alphabet_mismatches: vec![],
            state_count: 5,
        });
        let mut diags = Vec::new();
        lint_v01_vpa_determinizable(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }

    #[cfg(feature = "vpa")]
    #[test]
    fn v02_fires_on_mismatch() {
        let mut b = CtxBuilder::new();
        b.vpa_result_data = Some(crate::vpa::VpaAnalysis {
            is_determinizable: false,
            alphabet_mismatches: vec!["|".to_string()],
            state_count: 3,
        });
        let mut diags = Vec::new();
        lint_v02_vpa_alphabet_mismatch(&b.ctx(), &mut diags);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, "V02");
        assert_eq!(diags[0].severity, LintSeverity::Warning);
    }

    #[cfg(feature = "vpa")]
    #[test]
    fn v02_silent_when_no_mismatch() {
        let mut b = CtxBuilder::new();
        b.vpa_result_data = Some(crate::vpa::VpaAnalysis {
            is_determinizable: true,
            alphabet_mismatches: vec![],
            state_count: 3,
        });
        let mut diags = Vec::new();
        lint_v02_vpa_alphabet_mismatch(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }

    // ══════════════════════════════════════════════════════════════════════
    // V03-V04: WTA (feature = "tree-automata")
    // ══════════════════════════════════════════════════════════════════════

    #[cfg(feature = "tree-automata")]
    #[test]
    fn v03_fires_on_unrecognized() {
        let mut b = CtxBuilder::new();
        b.wta_result_data = Some(crate::tree_automaton::WtaAnalysis {
            unrecognized_terms: vec!["BadTerm".to_string()],
            hot_paths: vec![],
            state_count: 3,
            transition_count: 2,
        });
        let mut diags = Vec::new();
        lint_v03_wta_unrecognized_term(&b.ctx(), &mut diags);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, "V03");
        assert_eq!(diags[0].severity, LintSeverity::Warning);
    }

    #[cfg(feature = "tree-automata")]
    #[test]
    fn v03_silent_when_all_recognized() {
        let mut b = CtxBuilder::new();
        b.wta_result_data = Some(crate::tree_automaton::WtaAnalysis {
            unrecognized_terms: vec![],
            hot_paths: vec![],
            state_count: 3,
            transition_count: 2,
        });
        let mut diags = Vec::new();
        lint_v03_wta_unrecognized_term(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }

    #[cfg(feature = "tree-automata")]
    #[test]
    fn v04_fires_on_hot_path() {
        let mut b = CtxBuilder::new();
        b.wta_result_data = Some(crate::tree_automaton::WtaAnalysis {
            unrecognized_terms: vec![],
            hot_paths: vec!["Add→Int".to_string()],
            state_count: 3,
            transition_count: 2,
        });
        let mut diags = Vec::new();
        lint_v04_wta_hot_path(&b.ctx(), &mut diags);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, "V04");
        assert_eq!(diags[0].severity, LintSeverity::Note);
    }

    #[cfg(feature = "tree-automata")]
    #[test]
    fn v04_silent_when_no_hot_paths() {
        let mut b = CtxBuilder::new();
        b.wta_result_data = Some(crate::tree_automaton::WtaAnalysis {
            unrecognized_terms: vec![],
            hot_paths: vec![],
            state_count: 3,
            transition_count: 2,
        });
        let mut diags = Vec::new();
        lint_v04_wta_hot_path(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }

    // ══════════════════════════════════════════════════════════════════════
    // S04: EWPDS Merge Site (feature = "wpds-extended")
    // ══════════════════════════════════════════════════════════════════════

    #[cfg(feature = "wpds-extended")]
    #[test]
    fn s04_fires_with_merge_sites() {
        let mut b = CtxBuilder::new();
        b.ewpds_result_data = Some(crate::ewpds::EwpdsAnalysis {
            merge_site_count: 2,
            merge_site_labels: vec!["PNew".to_string(), "Match".to_string()],
        });
        let mut diags = Vec::new();
        lint_s04_ewpds_merge_site(&b.ctx(), &mut diags);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, "S04");
        assert_eq!(diags[0].severity, LintSeverity::Note);
    }

    #[cfg(feature = "wpds-extended")]
    #[test]
    fn s04_silent_when_no_sites() {
        let mut b = CtxBuilder::new();
        b.ewpds_result_data = Some(crate::ewpds::EwpdsAnalysis {
            merge_site_count: 0,
            merge_site_labels: vec![],
        });
        let mut diags = Vec::new();
        lint_s04_ewpds_merge_site(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }

    // ══════════════════════════════════════════════════════════════════════
    // S05: ARA Invariant (feature = "wpds-ara")
    // ══════════════════════════════════════════════════════════════════════

    #[cfg(feature = "wpds-ara")]
    #[test]
    fn s05_fires_with_ara() {
        let mut b = CtxBuilder::new();
        b.ara_result_data = Some(crate::ara::AraAnalysis {
            dimension: 3,
            invariant_count: 2,
            invariants: vec![
                ("Cat_A".to_string(), "x >= 0".to_string()),
                ("Cat_B".to_string(), "y <= 1".to_string()),
            ],
        });
        let mut diags = Vec::new();
        lint_s05_ara_invariant(&b.ctx(), &mut diags);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, "S05");
        assert_eq!(diags[0].severity, LintSeverity::Note);
    }

    #[cfg(feature = "wpds-ara")]
    #[test]
    fn s05_silent_when_none() {
        let b = CtxBuilder::new();
        let mut diags = Vec::new();
        lint_s05_ara_invariant(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }

    // ══════════════════════════════════════════════════════════════════════
    // N01-N02: Petri Net (feature = "petri")
    // ══════════════════════════════════════════════════════════════════════

    #[cfg(feature = "petri")]
    #[test]
    fn n01_fires_on_deadlock() {
        let mut b = CtxBuilder::new();
        b.petri_result_data = Some(crate::petri::PetriAnalysis {
            has_deadlock_risk: true,
            unbounded_places: vec![],
            place_count: 4,
            transition_count: 3,
        });
        let mut diags = Vec::new();
        lint_n01_deadlock_risk(&b.ctx(), &mut diags);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, "N01");
        assert_eq!(diags[0].severity, LintSeverity::Warning);
    }

    #[cfg(feature = "petri")]
    #[test]
    fn n01_silent_when_no_deadlock() {
        let mut b = CtxBuilder::new();
        b.petri_result_data = Some(crate::petri::PetriAnalysis {
            has_deadlock_risk: false,
            unbounded_places: vec![],
            place_count: 4,
            transition_count: 3,
        });
        let mut diags = Vec::new();
        lint_n01_deadlock_risk(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }

    #[cfg(feature = "petri")]
    #[test]
    fn n02_fires_on_unbounded() {
        let mut b = CtxBuilder::new();
        b.petri_result_data = Some(crate::petri::PetriAnalysis {
            has_deadlock_risk: false,
            unbounded_places: vec!["channel_in".to_string()],
            place_count: 4,
            transition_count: 3,
        });
        let mut diags = Vec::new();
        lint_n02_unbounded_channel(&b.ctx(), &mut diags);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, "N02");
        assert_eq!(diags[0].severity, LintSeverity::Warning);
    }

    #[cfg(feature = "petri")]
    #[test]
    fn n02_silent_when_bounded() {
        let mut b = CtxBuilder::new();
        b.petri_result_data = Some(crate::petri::PetriAnalysis {
            has_deadlock_risk: false,
            unbounded_places: vec![],
            place_count: 4,
            transition_count: 3,
        });
        let mut diags = Vec::new();
        lint_n02_unbounded_channel(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }

    // ══════════════════════════════════════════════════════════════════════
    // N03-N04: Nominal (feature = "nominal")
    // ══════════════════════════════════════════════════════════════════════

    #[cfg(feature = "nominal")]
    #[test]
    fn n03_fires_on_scope_violation() {
        let mut b = CtxBuilder::new();
        b.nominal_result_data = Some(crate::nominal::NominalAnalysis {
            scope_violations: vec![("x".to_string(), "rule Y".to_string())],
            narrowing_candidates: vec![],
            orbit_count: 1,
        });
        let mut diags = Vec::new();
        lint_n03_scope_violation(&b.ctx(), &mut diags);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, "N03");
        assert_eq!(diags[0].severity, LintSeverity::Warning);
    }

    #[cfg(feature = "nominal")]
    #[test]
    fn n03_silent_when_no_violations() {
        let mut b = CtxBuilder::new();
        b.nominal_result_data = Some(crate::nominal::NominalAnalysis {
            scope_violations: vec![],
            narrowing_candidates: vec![],
            orbit_count: 1,
        });
        let mut diags = Vec::new();
        lint_n03_scope_violation(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }

    #[cfg(feature = "nominal")]
    #[test]
    fn n04_fires_on_narrowing() {
        let mut b = CtxBuilder::new();
        b.nominal_result_data = Some(crate::nominal::NominalAnalysis {
            scope_violations: vec![],
            narrowing_candidates: vec![("x".to_string(), "narrow to inner scope".to_string())],
            orbit_count: 1,
        });
        let mut diags = Vec::new();
        lint_n04_scope_narrowing(&b.ctx(), &mut diags);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, "N04");
        assert_eq!(diags[0].severity, LintSeverity::Note);
    }

    #[cfg(feature = "nominal")]
    #[test]
    fn n04_silent_when_no_candidates() {
        let mut b = CtxBuilder::new();
        b.nominal_result_data = Some(crate::nominal::NominalAnalysis {
            scope_violations: vec![],
            narrowing_candidates: vec![],
            orbit_count: 1,
        });
        let mut diags = Vec::new();
        lint_n04_scope_narrowing(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }

    // ══════════════════════════════════════════════════════════════════════
    // N05: Alternating Bisimulation (feature = "alternating")
    // ══════════════════════════════════════════════════════════════════════

    #[cfg(feature = "alternating")]
    #[test]
    fn n05_fires_on_non_bisimilar() {
        let mut b = CtxBuilder::new();
        b.alternating_result_data = Some(crate::alternating::AlternatingAnalysis {
            non_bisimilar_pairs: vec![("Proc".to_string(), "Name".to_string())],
            state_count: 4,
        });
        let mut diags = Vec::new();
        lint_n05_non_bisimilar(&b.ctx(), &mut diags);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, "N05");
        assert_eq!(diags[0].severity, LintSeverity::Warning);
    }

    #[cfg(feature = "alternating")]
    #[test]
    fn n05_silent_when_bisimilar() {
        let mut b = CtxBuilder::new();
        b.alternating_result_data = Some(crate::alternating::AlternatingAnalysis {
            non_bisimilar_pairs: vec![],
            state_count: 4,
        });
        let mut diags = Vec::new();
        lint_n05_non_bisimilar(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }

    // ══════════════════════════════════════════════════════════════════════
    // L01-L02: LTL (feature = "ltl")
    // ══════════════════════════════════════════════════════════════════════

    #[cfg(feature = "ltl")]
    #[test]
    fn l01_fires_on_violated() {
        let mut b = CtxBuilder::new();
        b.ltl_results_data = Some(vec![crate::ltl::LtlCheckResult::Violated {
            prefix: vec!["cat_A".to_string()],
            lasso: vec!["loop".to_string()],
        }]);
        let mut diags = Vec::new();
        lint_l01_ltl_violated(&b.ctx(), &mut diags);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, "L01");
        assert_eq!(diags[0].severity, LintSeverity::Warning);
    }

    #[cfg(feature = "ltl")]
    #[test]
    fn l01_silent_when_satisfied() {
        let mut b = CtxBuilder::new();
        b.ltl_results_data = Some(vec![crate::ltl::LtlCheckResult::Satisfied]);
        let mut diags = Vec::new();
        lint_l01_ltl_violated(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }

    #[cfg(feature = "ltl")]
    #[test]
    fn l02_fires_when_satisfied() {
        let mut b = CtxBuilder::new();
        b.ltl_results_data = Some(vec![crate::ltl::LtlCheckResult::Satisfied]);
        let mut diags = Vec::new();
        lint_l02_ltl_verified(&b.ctx(), &mut diags);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, "L02");
        assert_eq!(diags[0].severity, LintSeverity::Note);
    }

    #[cfg(feature = "ltl")]
    #[test]
    fn l02_silent_when_violated() {
        let mut b = CtxBuilder::new();
        b.ltl_results_data = Some(vec![crate::ltl::LtlCheckResult::Violated {
            prefix: vec!["cat_A".to_string()],
            lasso: vec!["loop".to_string()],
        }]);
        let mut diags = Vec::new();
        lint_l02_ltl_verified(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }

    // ══════════════════════════════════════════════════════════════════════
    // E01: Provenance Trace (feature = "provenance")
    // ══════════════════════════════════════════════════════════════════════

    #[cfg(feature = "provenance")]
    #[test]
    fn e01_fires_with_traces() {
        let mut b = CtxBuilder::new();
        b.provenance_result_data = Some(crate::provenance::ProvenanceAnalysis {
            provenance_traces: vec![("rule1".to_string(), "x + y".to_string())],
        });
        let mut diags = Vec::new();
        lint_e01_provenance_trace(&b.ctx(), &mut diags);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, "E01");
        assert_eq!(diags[0].severity, LintSeverity::Note);
    }

    #[cfg(feature = "provenance")]
    #[test]
    fn e01_silent_when_no_traces() {
        let mut b = CtxBuilder::new();
        b.provenance_result_data = Some(crate::provenance::ProvenanceAnalysis {
            provenance_traces: vec![],
        });
        let mut diags = Vec::new();
        lint_e01_provenance_trace(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }

    // ══════════════════════════════════════════════════════════════════════
    // E02: CRA Cost Anomaly (feature = "cra")
    // ══════════════════════════════════════════════════════════════════════

    #[cfg(feature = "cra")]
    #[test]
    fn e02_fires_on_anomaly() {
        let mut b = CtxBuilder::new();
        b.cra_result_data = Some(crate::cra::CraAnalysis {
            cost_anomalies: vec![("register_0".to_string(), "999".to_string())],
            state_count: 3,
            register_count: 2,
        });
        let mut diags = Vec::new();
        lint_e02_cra_cost_anomaly(&b.ctx(), &mut diags);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, "E02");
        assert_eq!(diags[0].severity, LintSeverity::Warning);
    }

    #[cfg(feature = "cra")]
    #[test]
    fn e02_silent_when_no_anomalies() {
        let mut b = CtxBuilder::new();
        b.cra_result_data = Some(crate::cra::CraAnalysis {
            cost_anomalies: vec![],
            state_count: 3,
            register_count: 2,
        });
        let mut diags = Vec::new();
        lint_e02_cra_cost_anomaly(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }

    // ══════════════════════════════════════════════════════════════════════
    // M01-M02: Morphism (feature = "morphisms")
    // ══════════════════════════════════════════════════════════════════════

    #[cfg(feature = "morphisms")]
    #[test]
    fn m01_fires_on_gap() {
        let mut b = CtxBuilder::new();
        b.morphism_result_data = Some(crate::morphism::MorphismCheck {
            gaps: vec![crate::morphism::MorphismGap {
                kind: crate::morphism::GapKind::MissingSort,
                source_name: "Bool".to_string(),
                description: "no target sort for Bool".to_string(),
            }],
            preservation_failures: vec![],
            is_complete: false,
        });
        let mut diags = Vec::new();
        lint_m01_morphism_gap(&b.ctx(), &mut diags);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, "M01");
        assert_eq!(diags[0].severity, LintSeverity::Warning);
    }

    #[cfg(feature = "morphisms")]
    #[test]
    fn m01_silent_when_complete() {
        let mut b = CtxBuilder::new();
        b.morphism_result_data = Some(crate::morphism::MorphismCheck {
            gaps: vec![],
            preservation_failures: vec![],
            is_complete: true,
        });
        let mut diags = Vec::new();
        lint_m01_morphism_gap(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }

    #[cfg(feature = "morphisms")]
    #[test]
    fn m02_fires_on_failure() {
        let mut b = CtxBuilder::new();
        b.morphism_result_data = Some(crate::morphism::MorphismCheck {
            gaps: vec![],
            preservation_failures: vec!["eq1 not preserved".to_string()],
            is_complete: true,
        });
        let mut diags = Vec::new();
        lint_m02_morphism_preservation_failure(&b.ctx(), &mut diags);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, "M02");
        assert_eq!(diags[0].severity, LintSeverity::Warning);
    }

    #[cfg(feature = "morphisms")]
    #[test]
    fn m02_silent_when_preserved() {
        let mut b = CtxBuilder::new();
        b.morphism_result_data = Some(crate::morphism::MorphismCheck {
            gaps: vec![],
            preservation_failures: vec![],
            is_complete: true,
        });
        let mut diags = Vec::new();
        lint_m02_morphism_preservation_failure(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }

    // ══════════════════════════════════════════════════════════════════════
    // K01-K02: KAT (feature = "kat")
    // ══════════════════════════════════════════════════════════════════════

    #[cfg(feature = "kat")]
    #[test]
    fn k01_fires_on_hoare_failure() {
        let mut b = CtxBuilder::new();
        b.kat_result_data = Some(crate::kat::KatCheck {
            hoare_results: vec![("triple1".to_string(), false)],
            equivalence_results: vec![],
        });
        let mut diags = Vec::new();
        lint_k01_hoare_failure(&b.ctx(), &mut diags);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, "K01");
        assert_eq!(diags[0].severity, LintSeverity::Warning);
    }

    #[cfg(feature = "kat")]
    #[test]
    fn k01_silent_when_hoare_passes() {
        let mut b = CtxBuilder::new();
        b.kat_result_data = Some(crate::kat::KatCheck {
            hoare_results: vec![("triple1".to_string(), true)],
            equivalence_results: vec![],
        });
        let mut diags = Vec::new();
        lint_k01_hoare_failure(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }

    #[cfg(feature = "kat")]
    #[test]
    fn k02_fires_with_equivalence() {
        let mut b = CtxBuilder::new();
        b.kat_result_data = Some(crate::kat::KatCheck {
            hoare_results: vec![],
            equivalence_results: vec![("e1".to_string(), "e2".to_string(), true)],
        });
        let mut diags = Vec::new();
        lint_k02_kat_equivalence(&b.ctx(), &mut diags);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, "K02");
        assert_eq!(diags[0].severity, LintSeverity::Note);
    }

    #[cfg(feature = "kat")]
    #[test]
    fn k02_silent_when_none() {
        let b = CtxBuilder::new();
        let mut diags = Vec::new();
        lint_k02_kat_equivalence(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }
}
