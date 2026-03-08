//! D1: Cost-Benefit Optimization Framework
//!
//! Uses `ProductWeight<TropicalWeight, TropicalWeight>` (lexicographic ordering)
//! to rank optimization candidates by (speedup, compile_cost). Among equally
//! beneficial optimizations, the cheaper one is preferred.
//!
//! The framework evaluates grammar properties (shared prefix ratio, cold dispatch
//! fraction, ambiguous token fraction, etc.) and produces a ranked list of
//! optimizations that should be applied. Each optimization has:
//!
//! - **Speedup estimate** (lower = more beneficial, in tropical semiring)
//! - **Compile cost estimate** (lower = cheaper, in tropical semiring)
//! - **Applicability predicate** (gated on grammar analysis results)
//!
//! This module is purely analytical — it does not apply optimizations itself.
//! The pipeline consults `evaluate_optimizations()` to decide which passes to run.

use std::collections::HashMap;
use std::fmt;

use crate::automata::semiring::{ProductWeight, TropicalWeight};
use crate::prediction::FirstSet;
use crate::wfst::PredictionWfst;

/// An optimization that the framework can recommend.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Optimization {
    /// A1: Grammar left-factoring via prefix sharing.
    /// Subsumed by the decision tree for the DisjointSuffix path, but this
    /// gate still controls the recovery parser's legacy fallback.
    LeftFactoring,
    /// A2: Hot/cold dispatch path splitting
    HotColdSplitting,
    /// A4: Enhanced dead-code elimination via full dispatch graph
    EnhancedDeadCodeElimination,
    /// A5: CountingWeight-guided ambiguity targeting
    AmbiguityTargeting,
    /// B1: Multi-token lookahead via extended PredictionWfst.
    /// Used by both DT-driven NfaTryAll path and legacy fallback path.
    MultiTokenLookahead,
    /// B2: Adaptive recovery via runtime weight accumulation
    AdaptiveRecovery,
    /// B3: PredictionWfst minimization
    WfstMinimization,
    /// F1: Weight-based spillover pruning
    SpilloverPruning,
    /// F2: Early termination on deterministic hit
    EarlyTermination,
    /// F3: Lazy spillover (demand-driven replay)
    LazySpillover,
    /// G1: Backtracking elimination via compile-time FIRST set analysis.
    /// Used by both DT-driven NfaTryAll path (suffix_disjointness_check)
    /// and legacy fallback path.
    BacktrackingElimination,
    /// H1: ContextWeight-based disambiguation (Sprint 6).
    /// Uses powerset WFST to narrow NFA try-all candidate sets at compile time.
    ContextDisambiguation,
    /// G25: WPDS stack-aware reachability check.
    /// Uses poststar saturation to confirm/refute WFST-based dead-rule detection
    /// with full pushdown precision.
    WpdsReachabilityCheck,
    /// TRS confluence check: Knuth-Bendix critical pair analysis.
    TrsConfluenceCheck,
    /// VPA inclusion check: decidable structured sublanguage verification.
    VpaInclusionCheck,
    /// Safety verification: WPDS prestar against bad-state automaton.
    SafetyVerification,
    /// CEGAR refinement: iterative abstraction refinement loop.
    CegarRefinement,
    /// Petri net deadlock check: coverability analysis for concurrent patterns.
    PetriDeadlockCheck,
}

impl fmt::Display for Optimization {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::LeftFactoring => write!(f, "A1:LeftFactoring"),
            Self::HotColdSplitting => write!(f, "A2:HotColdSplitting"),
            Self::EnhancedDeadCodeElimination => write!(f, "A4:EnhancedDCE"),
            Self::AmbiguityTargeting => write!(f, "A5:AmbiguityTargeting"),
            Self::MultiTokenLookahead => write!(f, "B1:MultiTokenLookahead"),
            Self::AdaptiveRecovery => write!(f, "B2:AdaptiveRecovery"),
            Self::WfstMinimization => write!(f, "B3:WfstMinimization"),
            Self::SpilloverPruning => write!(f, "F1:SpilloverPruning"),
            Self::EarlyTermination => write!(f, "F2:EarlyTermination"),
            Self::LazySpillover => write!(f, "F3:LazySpillover"),
            Self::BacktrackingElimination => write!(f, "G1:BacktrackingElimination"),
            Self::ContextDisambiguation => write!(f, "H1:ContextDisambiguation"),
            Self::WpdsReachabilityCheck => write!(f, "G25:WpdsReachabilityCheck"),
            Self::TrsConfluenceCheck => write!(f, "T01:TrsConfluenceCheck"),
            Self::VpaInclusionCheck => write!(f, "V01:VpaInclusionCheck"),
            Self::SafetyVerification => write!(f, "S01:SafetyVerification"),
            Self::CegarRefinement => write!(f, "S03:CegarRefinement"),
            Self::PetriDeadlockCheck => write!(f, "N01:PetriDeadlockCheck"),
        }
    }
}

impl std::str::FromStr for Optimization {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s.trim() {
            // Short codes
            "A1" => Ok(Self::LeftFactoring),
            "A2" => Ok(Self::HotColdSplitting),
            "A4" => Ok(Self::EnhancedDeadCodeElimination),
            "A5" => Ok(Self::AmbiguityTargeting),
            "B1" => Ok(Self::MultiTokenLookahead),
            "B2" => Ok(Self::AdaptiveRecovery),
            "B3" => Ok(Self::WfstMinimization),
            "F1" => Ok(Self::SpilloverPruning),
            "F2" => Ok(Self::EarlyTermination),
            "F3" => Ok(Self::LazySpillover),
            "G1" => Ok(Self::BacktrackingElimination),
            "H1" => Ok(Self::ContextDisambiguation),
            "G25" => Ok(Self::WpdsReachabilityCheck),
            // Full names (case-insensitive)
            s if s.eq_ignore_ascii_case("LeftFactoring") => Ok(Self::LeftFactoring),
            s if s.eq_ignore_ascii_case("HotColdSplitting") => Ok(Self::HotColdSplitting),
            s if s.eq_ignore_ascii_case("EnhancedDeadCodeElimination")
                || s.eq_ignore_ascii_case("EnhancedDCE") =>
            {
                Ok(Self::EnhancedDeadCodeElimination)
            },
            s if s.eq_ignore_ascii_case("AmbiguityTargeting") => Ok(Self::AmbiguityTargeting),
            s if s.eq_ignore_ascii_case("MultiTokenLookahead") => Ok(Self::MultiTokenLookahead),
            s if s.eq_ignore_ascii_case("AdaptiveRecovery") => Ok(Self::AdaptiveRecovery),
            s if s.eq_ignore_ascii_case("WfstMinimization") => Ok(Self::WfstMinimization),
            s if s.eq_ignore_ascii_case("SpilloverPruning") => Ok(Self::SpilloverPruning),
            s if s.eq_ignore_ascii_case("EarlyTermination") => Ok(Self::EarlyTermination),
            s if s.eq_ignore_ascii_case("LazySpillover") => Ok(Self::LazySpillover),
            s if s.eq_ignore_ascii_case("BacktrackingElimination") => Ok(Self::BacktrackingElimination),
            s if s.eq_ignore_ascii_case("ContextDisambiguation") => Ok(Self::ContextDisambiguation),
            s if s.eq_ignore_ascii_case("WpdsReachabilityCheck") => Ok(Self::WpdsReachabilityCheck),
            "T01" => Ok(Self::TrsConfluenceCheck),
            s if s.eq_ignore_ascii_case("TrsConfluenceCheck") => Ok(Self::TrsConfluenceCheck),
            "V01" => Ok(Self::VpaInclusionCheck),
            s if s.eq_ignore_ascii_case("VpaInclusionCheck") => Ok(Self::VpaInclusionCheck),
            "S01" => Ok(Self::SafetyVerification),
            s if s.eq_ignore_ascii_case("SafetyVerification") => Ok(Self::SafetyVerification),
            "S03" => Ok(Self::CegarRefinement),
            s if s.eq_ignore_ascii_case("CegarRefinement") => Ok(Self::CegarRefinement),
            "N01" => Ok(Self::PetriDeadlockCheck),
            s if s.eq_ignore_ascii_case("PetriDeadlockCheck") => Ok(Self::PetriDeadlockCheck),
            // Display format: "A1:LeftFactoring"
            s if s.contains(':') => s
                .split_once(':')
                .map(|(code, _)| code)
                .unwrap_or(s)
                .parse(),
            other => Err(format!("unknown optimization: '{}'. Valid values: A1, A2, A4, A5, B1, B2, B3, F1, F2, F3, G1, H1, G25, T01, V01, S01, S03, N01", other)),
        }
    }
}

/// A candidate optimization with cost-benefit analysis.
#[derive(Debug, Clone)]
pub struct OptimizationCandidate {
    /// Which optimization this is.
    pub optimization: Optimization,
    /// Estimated speedup (tropical: lower = more speedup).
    pub speedup: TropicalWeight,
    /// Estimated compile cost (tropical: lower = cheaper).
    pub compile_cost: TropicalWeight,
    /// Combined score: `ProductWeight<speedup, compile_cost>` with lexicographic
    /// ordering. Lower is better.
    pub score: ProductWeight<TropicalWeight, TropicalWeight>,
    /// Whether this optimization is applicable to the current grammar.
    pub applicable: bool,
    /// Human-readable reason for applicability decision.
    pub reason: String,
}

impl OptimizationCandidate {
    fn new(
        optimization: Optimization,
        speedup: f64,
        compile_cost: f64,
        applicable: bool,
        reason: String,
    ) -> Self {
        let speedup_w = TropicalWeight::new(speedup);
        let compile_cost_w = TropicalWeight::new(compile_cost);
        OptimizationCandidate {
            optimization,
            speedup: speedup_w,
            compile_cost: compile_cost_w,
            score: ProductWeight::new(speedup_w, compile_cost_w),
            applicable,
            reason,
        }
    }
}

/// Grammar profile extracted from WFST analysis and PathMap decision trees.
///
/// Computed once during pipeline execution and passed to `evaluate_optimizations()`.
#[derive(Debug, Clone)]
pub struct GrammarProfile {
    /// Fraction of dispatch tokens that share a prefix with another rule (0.0..1.0).
    pub shared_prefix_ratio: f64,
    /// Fraction of dispatch arms with weight >= cold threshold (0.0..1.0).
    pub cold_fraction: f64,
    /// Fraction of dispatch tokens that are ambiguous (CountingWeight > 1) (0.0..1.0).
    pub ambiguous_fraction: f64,
    /// Number of ambiguous dispatch tokens across all categories.
    pub ambiguous_count: usize,
    /// Total number of categories in the grammar.
    pub category_count: usize,
    /// Total number of rules in the grammar.
    pub rule_count: usize,
    /// Number of categories requiring NFA spillover.
    pub nfa_spillover_categories: usize,
    /// Whether beam width is configured.
    pub has_beam_width: bool,
    /// Number of PredictionWfst states (sum across all categories).
    pub total_wfst_states: usize,

    // ── PathMap decision tree metrics ─────────────────────────────────────
    /// Mean max_depth across all category decision trees.
    pub avg_trie_depth: f64,
    /// Fraction of ambiguous nodes across all decision trees (ambiguous / total_states).
    pub ambiguity_score: f64,
    /// Fraction of rules that have fully deterministic dispatch (no ambiguity at prefix).
    pub deterministic_ratio: f64,
}

/// Build a `GrammarProfile` from pipeline data and decision tree metrics.
///
/// This is the main analysis entry point, called from the pipeline after
/// WFST and decision tree construction.
pub fn build_grammar_profile(
    prediction_wfsts: &HashMap<String, PredictionWfst>,
    first_sets: &HashMap<String, FirstSet>,
    nfa_spillover_cats: &std::collections::HashSet<String>,
    rule_count: usize,
    has_beam_width: bool,
    decision_trees: &HashMap<String, crate::decision_tree::CategoryDecisionTree>,
) -> GrammarProfile {
    let category_count = prediction_wfsts.len();

    // Count ambiguous dispatch tokens (prediction returns > 1 action for a token)
    let mut total_dispatch_tokens = 0usize;
    let mut ambiguous_tokens = 0usize;

    for (cat, wfst) in prediction_wfsts {
        if let Some(first_set) = first_sets.get(cat) {
            for token in &first_set.tokens {
                total_dispatch_tokens += 1;
                let predictions = wfst.predict(token);
                if predictions.len() > 1 {
                    ambiguous_tokens += 1;
                }
            }
        }
    }

    let ambiguous_fraction = if total_dispatch_tokens > 0 {
        ambiguous_tokens as f64 / total_dispatch_tokens as f64
    } else {
        0.0
    };

    // Cold fraction: count dispatch actions with weight >= 1.0
    let mut total_actions = 0usize;
    let mut cold_actions = 0usize;

    for wfst in prediction_wfsts.values() {
        for action in &wfst.actions {
            total_actions += 1;
            if action.weight.value() >= 1.0 {
                cold_actions += 1;
            }
        }
    }

    let cold_fraction = if total_actions > 0 {
        cold_actions as f64 / total_actions as f64
    } else {
        0.0
    };

    // Shared prefix ratio: count NFA-ambiguous categories / total
    let shared_prefix_ratio = if category_count > 0 {
        nfa_spillover_cats.len() as f64 / category_count as f64
    } else {
        0.0
    };

    // Total WFST states
    let total_wfst_states: usize = prediction_wfsts.values().map(|w| w.states.len()).sum();

    // PathMap decision tree metrics
    let (avg_trie_depth, ambiguity_score, deterministic_ratio) = if decision_trees.is_empty() {
        (0.0, 0.0, 1.0)
    } else {
        let mut total_depth = 0usize;
        let mut total_ambiguous = 0usize;
        let mut total_states = 0usize;
        let mut total_det_rules = 0usize;
        let mut total_rules = 0usize;
        for tree in decision_trees.values() {
            total_depth += tree.stats.max_depth;
            total_ambiguous += tree.stats.ambiguous_nodes;
            total_states += tree.stats.total_states;
            total_det_rules += tree.stats.deterministic_rules;
            total_rules += tree.stats.total_rules;
        }
        let n = decision_trees.len() as f64;
        (
            total_depth as f64 / n,
            if total_states > 0 { total_ambiguous as f64 / total_states as f64 } else { 0.0 },
            if total_rules > 0 { total_det_rules as f64 / total_rules as f64 } else { 1.0 },
        )
    };

    GrammarProfile {
        shared_prefix_ratio,
        cold_fraction,
        ambiguous_fraction,
        ambiguous_count: ambiguous_tokens,
        category_count,
        rule_count,
        nfa_spillover_categories: nfa_spillover_cats.len(),
        has_beam_width,
        total_wfst_states,
        avg_trie_depth,
        ambiguity_score,
        deterministic_ratio,
    }
}

/// Evaluate all optimizations against the grammar profile.
///
/// Returns candidates sorted by score (best first, via lexicographic ordering
/// on `ProductWeight<speedup, compile_cost>`). Only `applicable` candidates
/// should be acted upon.
pub fn evaluate_optimizations(profile: &GrammarProfile) -> Vec<OptimizationCandidate> {
    let mut candidates = Vec::with_capacity(10);

    // A1: Left-factoring — beneficial when many rules share prefixes
    candidates.push(OptimizationCandidate::new(
        Optimization::LeftFactoring,
        // speedup: -ln(shared_prefix_ratio) — more sharing = lower (better) weight
        if profile.shared_prefix_ratio > 0.0 {
            -profile.shared_prefix_ratio.ln()
        } else {
            f64::INFINITY
        },
        // cost: proportional to category count (each category may need factoring)
        profile.category_count as f64 * 0.1,
        profile.shared_prefix_ratio > 0.3,
        format!(
            "shared_prefix_ratio={:.2} (threshold: >0.3)",
            profile.shared_prefix_ratio
        ),
    ));

    // A2: Hot/cold splitting — beneficial when many dispatch arms are cold
    candidates.push(OptimizationCandidate::new(
        Optimization::HotColdSplitting,
        // speedup: -ln(cold_fraction)
        if profile.cold_fraction > 0.0 {
            -profile.cold_fraction.ln()
        } else {
            f64::INFINITY
        },
        0.05, // fixed low cost
        profile.cold_fraction > 0.4,
        format!(
            "cold_fraction={:.2} (threshold: >0.4)",
            profile.cold_fraction
        ),
    ));

    // A4: Enhanced DCE — always beneficial for grammar validation
    candidates.push(OptimizationCandidate::new(
        Optimization::EnhancedDeadCodeElimination,
        0.5, // moderate speedup (removes dead codegen)
        0.2, // low-medium cost
        profile.rule_count > 5,
        format!("rule_count={} (threshold: >5)", profile.rule_count),
    ));

    // A5: Ambiguity targeting — enables B1, useful when there's ambiguity
    candidates.push(OptimizationCandidate::new(
        Optimization::AmbiguityTargeting,
        if profile.ambiguous_fraction > 0.0 {
            -profile.ambiguous_fraction.ln()
        } else {
            f64::INFINITY
        },
        0.1, // low cost (analysis only)
        profile.ambiguous_fraction > 0.1,
        format!(
            "ambiguous_fraction={:.2} (threshold: >0.1)",
            profile.ambiguous_fraction
        ),
    ));

    // B1: Multi-token lookahead — beneficial for ambiguous grammars with few tokens
    candidates.push(OptimizationCandidate::new(
        Optimization::MultiTokenLookahead,
        if profile.ambiguous_fraction > 0.0 {
            -profile.ambiguous_fraction.ln()
        } else {
            f64::INFINITY
        },
        profile.ambiguous_count as f64 * 0.5,
        profile.ambiguous_fraction > 0.1 && profile.ambiguous_count < 10,
        format!(
            "ambiguous_fraction={:.2}, ambiguous_count={} (thresholds: >0.1, <10)",
            profile.ambiguous_fraction, profile.ambiguous_count
        ),
    ));

    // B2: Adaptive recovery — always applicable, zero happy-path cost
    candidates.push(OptimizationCandidate::new(
        Optimization::AdaptiveRecovery,
        0.3, // modest benefit (error path only)
        0.1, // low cost
        true,
        "always applicable (zero happy-path overhead)".to_string(),
    ));

    // B3: WFST minimization — beneficial when WFST has many states
    candidates.push(OptimizationCandidate::new(
        Optimization::WfstMinimization,
        if profile.total_wfst_states > 0 {
            -(profile.total_wfst_states as f64).ln()
        } else {
            f64::INFINITY
        },
        0.15,
        profile.total_wfst_states > 4,
        format!(
            "total_wfst_states={} (threshold: >4)",
            profile.total_wfst_states
        ),
    ));

    // F1: Spillover pruning — beneficial when beam is set and there's spillover
    candidates.push(OptimizationCandidate::new(
        Optimization::SpilloverPruning,
        0.2, // low weight = high benefit
        0.01, // trivial cost
        profile.has_beam_width && profile.nfa_spillover_categories > 0,
        format!(
            "has_beam_width={}, nfa_spillover_categories={}",
            profile.has_beam_width, profile.nfa_spillover_categories
        ),
    ));

    // F2: Early termination — beneficial when deterministic alternatives exist
    candidates.push(OptimizationCandidate::new(
        Optimization::EarlyTermination,
        0.1, // very beneficial
        0.01, // trivial cost
        profile.nfa_spillover_categories == 0 && profile.ambiguous_count > 0,
        format!(
            "nfa_spillover_categories={}, ambiguous_count={}",
            profile.nfa_spillover_categories, profile.ambiguous_count
        ),
    ));

    // F3: Lazy spillover — beneficial when there's spillover
    candidates.push(OptimizationCandidate::new(
        Optimization::LazySpillover,
        0.3,
        0.3, // medium cost (refactoring parse_preserving_vars)
        profile.nfa_spillover_categories > 0,
        format!(
            "nfa_spillover_categories={}",
            profile.nfa_spillover_categories
        ),
    ));

    // G1: Backtracking elimination — always beneficial (removes redundant save/restore)
    candidates.push(OptimizationCandidate::new(
        Optimization::BacktrackingElimination,
        0.2, // good speedup (eliminates speculative parses)
        0.1, // low cost (compile-time FIRST set analysis)
        true,
        "always applicable (static FIRST set analysis)".to_string(),
    ));

    // H1: ContextWeight-based disambiguation
    candidates.push(OptimizationCandidate::new(
        Optimization::ContextDisambiguation,
        if profile.ambiguous_fraction > 0.0 {
            -profile.ambiguous_fraction.ln() * 0.8
        } else {
            f64::INFINITY
        },
        0.2,
        profile.nfa_spillover_categories > 0 && profile.ambiguous_fraction > 0.05,
        format!(
            "nfa_spillover_categories={}, ambiguous_fraction={:.2}",
            profile.nfa_spillover_categories, profile.ambiguous_fraction
        ),
    ));

    // G25: WPDS stack-aware reachability — beneficial for multi-category grammars
    candidates.push(OptimizationCandidate::new(
        Optimization::WpdsReachabilityCheck,
        0.4, // moderate benefit (refines dead-rule detection)
        0.3, // medium cost (WPDS construction + poststar saturation)
        profile.category_count >= 2,
        format!(
            "category_count={} (threshold: >=2)",
            profile.category_count
        ),
    ));

    // T01: TRS confluence check — beneficial when rules have overlapping patterns
    candidates.push(OptimizationCandidate::new(
        Optimization::TrsConfluenceCheck,
        0.5, // diagnostic benefit (catches rewriting bugs)
        0.15, // low cost (critical pair enumeration)
        profile.rule_count > 3,
        format!("rule_count={} (threshold: >3)", profile.rule_count),
    ));

    // V01: VPA inclusion check — beneficial for grammars with delimiter structure
    candidates.push(OptimizationCandidate::new(
        Optimization::VpaInclusionCheck,
        0.6, // diagnostic benefit (identifies zero-backtracking sublanguage)
        0.1, // low cost (VPA construction)
        profile.category_count >= 1,
        format!(
            "category_count={} (threshold: >=1)",
            profile.category_count,
        ),
    ));

    // S01: Safety verification — beneficial when WPDS detects unreachable rules
    candidates.push(OptimizationCandidate::new(
        Optimization::SafetyVerification,
        0.3, // good benefit (confirms unreachability with prestar)
        0.25, // moderate cost (prestar saturation)
        profile.category_count >= 2,
        format!(
            "category_count={} (threshold: >=2)",
            profile.category_count,
        ),
    ));

    // S03: CEGAR refinement — beneficial when WPDS reports unreachable rules
    candidates.push(OptimizationCandidate::new(
        Optimization::CegarRefinement,
        0.45, // diagnostic benefit
        0.3, // medium cost (iterative refinement)
        profile.category_count >= 2,
        format!(
            "category_count={} (threshold: >=2)",
            profile.category_count,
        ),
    ));

    // N01: Petri net deadlock check — beneficial for grammars with parallel composition
    candidates.push(OptimizationCandidate::new(
        Optimization::PetriDeadlockCheck,
        0.7, // diagnostic benefit (deadlock detection)
        0.1, // low cost (coverability check)
        profile.rule_count > 5,
        format!("rule_count={} (threshold: >5)", profile.rule_count),
    ));

    // Sort by score (lexicographic: speedup first, then compile_cost)
    candidates.sort_by(|a, b| a.score.cmp(&b.score));

    candidates
}

/// Return only the applicable optimizations, sorted by score.
pub fn recommended_optimizations(profile: &GrammarProfile) -> Vec<OptimizationCandidate> {
    evaluate_optimizations(profile)
        .into_iter()
        .filter(|c| c.applicable)
        .collect()
}

// ══════════════════════════════════════════════════════════════════════════════
// A3: Optimization Gates — pipeline self-tuning via cost-benefit results
// ══════════════════════════════════════════════════════════════════════════════

/// Boolean gates for each optimization pass, derived from cost-benefit analysis.
///
/// The pipeline populates this from `recommended_optimizations()` and threads it
/// into `TrampolineConfig` and `write_category_dispatch()`. Each gate controls
/// whether the corresponding codegen optimization is emitted. When a gate is
/// `false`, the codegen falls back to the default (unoptimized) path for that
/// optimization, avoiding code bloat and compile overhead for grammars that
/// don't benefit from it.
#[derive(Debug, Clone)]
pub struct OptimizationGates {
    /// A1: Grammar left-factoring via shared terminal prefix extraction.
    /// When false, NFA try-all always emits full save/restore per alternative.
    pub left_factoring: bool,
    /// A2: Hot/cold dispatch path splitting in `write_category_dispatch()`.
    /// When false, all dispatch arms are inlined regardless of weight.
    pub hot_cold_splitting: bool,
    /// B1: Multi-token lookahead via second-token dispatch.
    /// When false, ambiguous prefix groups always use NFA try-all.
    pub multi_token_lookahead: bool,
    /// F1: Weight-based spillover pruning (beam-gated alternative filtering).
    /// When false, all position-matching alternatives are spilled regardless of weight.
    pub spillover_pruning: bool,
    /// F2: Early termination on deterministic hit (weight == 0.0).
    /// When false, all alternatives are always tried even if the first succeeds.
    pub early_termination: bool,
    /// F3: Lazy spillover (demand-driven forced-prefix replay).
    /// When false, spillover is eager (all alternatives replayed immediately).
    pub lazy_spillover: bool,
    /// B3: WFST minimization via TransducerCascade.
    /// When false, the cascade is not run after WFST construction.
    pub wfst_minimization: bool,
    /// A4: Enhanced dead-code elimination via forward-backward analysis.
    pub enhanced_dce: bool,
    /// A5: CountingWeight-guided ambiguity targeting.
    pub ambiguity_targeting: bool,
    /// B2: Adaptive recovery via runtime weight accumulation.
    pub adaptive_recovery: bool,
    /// G1: Backtracking elimination via compile-time FIRST set analysis.
    /// Controls Phases 1-4: deterministic cross-cat arm commit, NFA suffix
    /// disjointness, LParen LL(2)/LL(3), optional LL(1) guard.
    pub backtracking_elimination: bool,
    /// H1: ContextWeight-based disambiguation (Sprint 6).
    /// When true, NFA try-all codegen narrows candidates via ContextWeight.
    pub context_disambiguation: bool,
    /// G25: WPDS stack-aware reachability check.
    /// When true, poststar analysis refines dead-rule detection.
    pub wpds_reachability: bool,
    /// T01: TRS confluence check.
    #[cfg(feature = "trs-analysis")]
    pub trs_confluence: bool,
    /// V01: VPA inclusion check.
    #[cfg(feature = "vpa")]
    pub vpa_inclusion: bool,
    /// S01: Safety verification via WPDS prestar.
    pub safety_verification: bool,
    /// S03: CEGAR refinement loop.
    pub cegar_refinement: bool,
    /// N01: Petri net deadlock check.
    #[cfg(feature = "petri")]
    pub petri_deadlock: bool,
}

impl OptimizationGates {
    /// Create gates where all optimizations are enabled (for backward compatibility).
    pub fn all_enabled() -> Self {
        OptimizationGates {
            left_factoring: true,
            hot_cold_splitting: true,
            multi_token_lookahead: true,
            spillover_pruning: true,
            early_termination: true,
            lazy_spillover: true,
            wfst_minimization: true,
            enhanced_dce: true,
            ambiguity_targeting: true,
            adaptive_recovery: true,
            backtracking_elimination: true,
            context_disambiguation: true,
            wpds_reachability: true,
            #[cfg(feature = "trs-analysis")]
            trs_confluence: true,
            #[cfg(feature = "vpa")]
            vpa_inclusion: true,
            safety_verification: true,
            cegar_refinement: true,
            #[cfg(feature = "petri")]
            petri_deadlock: true,
        }
    }

    /// Populate gates from cost-benefit recommendations.
    ///
    /// Only optimizations that appear in `recommended` are enabled.
    /// All others default to `false`.
    pub fn from_recommendations(recommended: &[OptimizationCandidate]) -> Self {
        let enabled: std::collections::HashSet<Optimization> = recommended
            .iter()
            .map(|c| c.optimization)
            .collect();

        OptimizationGates {
            left_factoring: enabled.contains(&Optimization::LeftFactoring),
            hot_cold_splitting: enabled.contains(&Optimization::HotColdSplitting),
            multi_token_lookahead: enabled.contains(&Optimization::MultiTokenLookahead),
            spillover_pruning: enabled.contains(&Optimization::SpilloverPruning),
            early_termination: enabled.contains(&Optimization::EarlyTermination),
            lazy_spillover: enabled.contains(&Optimization::LazySpillover),
            wfst_minimization: enabled.contains(&Optimization::WfstMinimization),
            enhanced_dce: enabled.contains(&Optimization::EnhancedDeadCodeElimination),
            ambiguity_targeting: enabled.contains(&Optimization::AmbiguityTargeting),
            adaptive_recovery: enabled.contains(&Optimization::AdaptiveRecovery),
            backtracking_elimination: enabled.contains(&Optimization::BacktrackingElimination),
            context_disambiguation: enabled.contains(&Optimization::ContextDisambiguation),
            wpds_reachability: enabled.contains(&Optimization::WpdsReachabilityCheck),
            #[cfg(feature = "trs-analysis")]
            trs_confluence: enabled.contains(&Optimization::TrsConfluenceCheck),
            #[cfg(feature = "vpa")]
            vpa_inclusion: enabled.contains(&Optimization::VpaInclusionCheck),
            safety_verification: enabled.contains(&Optimization::SafetyVerification),
            cegar_refinement: enabled.contains(&Optimization::CegarRefinement),
            #[cfg(feature = "petri")]
            petri_deadlock: enabled.contains(&Optimization::PetriDeadlockCheck),
        }
    }

    /// Create gates where no optimizations are enabled.
    pub fn none_enabled() -> Self {
        OptimizationGates {
            left_factoring: false,
            hot_cold_splitting: false,
            multi_token_lookahead: false,
            spillover_pruning: false,
            early_termination: false,
            lazy_spillover: false,
            wfst_minimization: false,
            enhanced_dce: false,
            ambiguity_targeting: false,
            adaptive_recovery: false,
            backtracking_elimination: false,
            context_disambiguation: false,
            wpds_reachability: false,
            #[cfg(feature = "trs-analysis")]
            trs_confluence: false,
            #[cfg(feature = "vpa")]
            vpa_inclusion: false,
            safety_verification: false,
            cegar_refinement: false,
            #[cfg(feature = "petri")]
            petri_deadlock: false,
        }
    }

    /// Read optimization gates from the `PRATTAIL_AUTO_OPTIMIZE` environment variable.
    ///
    /// Returns:
    /// - `Ok(None)` if the variable is not set
    /// - `Ok(Some(gates))` on success
    /// - `Err(msg)` on parse failure
    ///
    /// Special values:
    /// - `all` — all optimizations enabled
    /// - `none` — all optimizations disabled
    ///
    /// Otherwise, a comma-separated list of optimization codes or names:
    /// `PRATTAIL_AUTO_OPTIMIZE=A1,B2,F3`
    pub fn from_env() -> Result<Option<Self>, String> {
        let val = match std::env::var("PRATTAIL_AUTO_OPTIMIZE") {
            Ok(v) => v,
            Err(std::env::VarError::NotPresent) => return Ok(None),
            Err(std::env::VarError::NotUnicode(_)) => {
                return Err("PRATTAIL_AUTO_OPTIMIZE contains non-UTF-8 data".to_string());
            },
        };

        let trimmed = val.trim();
        if trimmed.eq_ignore_ascii_case("all") {
            return Ok(Some(Self::all_enabled()));
        }
        if trimmed.eq_ignore_ascii_case("none") {
            return Ok(Some(Self::none_enabled()));
        }

        let mut enabled = std::collections::HashSet::new();
        for part in trimmed.split(',') {
            let part = part.trim();
            if part.is_empty() {
                continue;
            }
            let opt: Optimization = part.parse()?;
            enabled.insert(opt);
        }

        Ok(Some(OptimizationGates {
            left_factoring: enabled.contains(&Optimization::LeftFactoring),
            hot_cold_splitting: enabled.contains(&Optimization::HotColdSplitting),
            multi_token_lookahead: enabled.contains(&Optimization::MultiTokenLookahead),
            spillover_pruning: enabled.contains(&Optimization::SpilloverPruning),
            early_termination: enabled.contains(&Optimization::EarlyTermination),
            lazy_spillover: enabled.contains(&Optimization::LazySpillover),
            wfst_minimization: enabled.contains(&Optimization::WfstMinimization),
            enhanced_dce: enabled.contains(&Optimization::EnhancedDeadCodeElimination),
            ambiguity_targeting: enabled.contains(&Optimization::AmbiguityTargeting),
            adaptive_recovery: enabled.contains(&Optimization::AdaptiveRecovery),
            backtracking_elimination: enabled.contains(&Optimization::BacktrackingElimination),
            context_disambiguation: enabled.contains(&Optimization::ContextDisambiguation),
            wpds_reachability: enabled.contains(&Optimization::WpdsReachabilityCheck),
            #[cfg(feature = "trs-analysis")]
            trs_confluence: enabled.contains(&Optimization::TrsConfluenceCheck),
            #[cfg(feature = "vpa")]
            vpa_inclusion: enabled.contains(&Optimization::VpaInclusionCheck),
            safety_verification: enabled.contains(&Optimization::SafetyVerification),
            cegar_refinement: enabled.contains(&Optimization::CegarRefinement),
            #[cfg(feature = "petri")]
            petri_deadlock: enabled.contains(&Optimization::PetriDeadlockCheck),
        }))
    }

    /// Try env override first, fall back to cost-benefit recommendations.
    ///
    /// Logs a warning when the env override is active.
    pub fn from_env_or_recommendations(recommended: &[OptimizationCandidate]) -> Self {
        match Self::from_env() {
            Ok(Some(gates)) => {
                crate::lint::emit_diagnostic(&crate::lint::LintDiagnostic {
                    id: "I08",
                    name: "env-override-active",
                    severity: crate::lint::LintSeverity::Warning,
                    category: None,
                    rule: None,
                    message: "PRATTAIL_AUTO_OPTIMIZE override active — cost-benefit recommendations bypassed".to_string(),
                    hint: Some("unset PRATTAIL_AUTO_OPTIMIZE to use automatic cost-benefit analysis".to_string()),
                    grammar_name: None,
                    source_location: None,
                });
                gates
            },
            Ok(None) => Self::from_recommendations(recommended),
            Err(e) => {
                crate::lint::emit_diagnostic(&crate::lint::LintDiagnostic {
                    id: "I09",
                    name: "env-override-parse-error",
                    severity: crate::lint::LintSeverity::Error,
                    category: None,
                    rule: None,
                    message: format!("PRATTAIL_AUTO_OPTIMIZE parse error: {} — falling back to cost-benefit analysis", e),
                    hint: Some("valid values: `all`, `none`, or comma-separated optimization codes (e.g., `A1,B2,F3`)".to_string()),
                    grammar_name: None,
                    source_location: None,
                });
                Self::from_recommendations(recommended)
            },
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// A5: Ambiguity Targeting Analysis
// ══════════════════════════════════════════════════════════════════════════════

/// Per-token ambiguity analysis for a single category.
///
/// Identifies which dispatch tokens are ambiguous (multiple rules match) and
/// computes the ambiguity count for each. Used by:
/// - B1 (multi-token lookahead) to select tokens that need extended WFSTs
/// - NFA spillover to pre-size buffers
/// - Grammar diagnostics to report per-token ambiguity
#[derive(Debug, Clone)]
pub struct TokenAmbiguityInfo {
    /// Category this token belongs to.
    pub category: String,
    /// Token variant name (e.g., "Ident", "LParen").
    pub token: String,
    /// Number of dispatch alternatives for this token (CountingWeight value).
    pub alternative_count: u64,
    /// Rule labels that match this token.
    pub rule_labels: Vec<String>,
    /// Whether this token is a candidate for multi-token lookahead (B1).
    /// True when alternative_count > 1 and the alternatives differ on
    /// their second token.
    pub lookahead_candidate: bool,
}

/// Result of A5 ambiguity targeting analysis.
#[derive(Debug, Clone)]
pub struct AmbiguityTargetingResult {
    /// All ambiguous tokens across all categories.
    pub ambiguous_tokens: Vec<TokenAmbiguityInfo>,
    /// Total number of unambiguous tokens (for reporting).
    pub unambiguous_count: usize,
    /// Maximum ambiguity count observed across all tokens.
    pub max_ambiguity: u64,
    /// Categories where NFA spillover buffer should be pre-sized.
    pub presized_categories: Vec<(String, usize)>,
}

/// Perform A5 ambiguity targeting analysis.
///
/// Scans all prediction WFSTs and identifies per-token ambiguity using
/// `predict_with_confidence()`. Returns structured analysis that downstream
/// optimizations (B1, F3) can consume.
///
/// The `ambiguity_threshold` parameter controls which tokens are flagged
/// as candidates for multi-token lookahead (B1). Tokens with
/// `alternative_count > threshold` are flagged.
pub fn analyze_ambiguity_targets(
    prediction_wfsts: &HashMap<String, PredictionWfst>,
    first_sets: &HashMap<String, FirstSet>,
    ambiguity_threshold: u64,
) -> AmbiguityTargetingResult {
    let mut ambiguous_tokens = Vec::new();
    let mut unambiguous_count = 0usize;
    let mut max_ambiguity = 0u64;
    let mut category_max_ambiguity: HashMap<String, usize> = HashMap::new();

    for (cat, wfst) in prediction_wfsts {
        if let Some(first_set) = first_sets.get(cat) {
            let mut cat_max = 0usize;

            for token in first_set.sorted_tokens() {
                let predictions = wfst.predict_with_confidence(&token);
                let count = predictions.first().map_or(0, |(_, cw)| cw.count());

                if count > 1 {
                    let rule_labels: Vec<String> = predictions
                        .iter()
                        .map(|(a, _)| a.action.rule_label().to_string())
                        .collect();

                    let lookahead_candidate = count > ambiguity_threshold;

                    ambiguous_tokens.push(TokenAmbiguityInfo {
                        category: cat.clone(),
                        token: token.to_string(),
                        alternative_count: count,
                        rule_labels,
                        lookahead_candidate,
                    });

                    if count > max_ambiguity {
                        max_ambiguity = count;
                    }

                    cat_max = cat_max.max(count as usize);
                } else {
                    unambiguous_count += 1;
                }
            }

            if cat_max > 0 {
                category_max_ambiguity.insert(cat.clone(), cat_max);
            }
        }
    }

    // Pre-size NFA spillover buffers based on maximum ambiguity per category
    let presized_categories: Vec<(String, usize)> = category_max_ambiguity
        .into_iter()
        .map(|(cat, max)| (cat, max.saturating_sub(1))) // N-1 alternatives spilled
        .collect();

    AmbiguityTargetingResult {
        ambiguous_tokens,
        unambiguous_count,
        max_ambiguity,
        presized_categories,
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// D2: Grammar Complexity Report
// ══════════════════════════════════════════════════════════════════════════════

/// D2: Per-category complexity metrics for the grammar complexity report.
#[derive(Debug, Clone)]
pub struct CategoryComplexity {
    /// Category name.
    pub name: String,
    /// Number of dispatch tokens in FIRST set.
    pub dispatch_token_count: usize,
    /// Number of ambiguous dispatch tokens (>1 action).
    pub ambiguous_token_count: usize,
    /// Maximum ambiguity factor (most alternatives for any single token).
    pub max_ambiguity: usize,
    /// Number of WFST states.
    pub wfst_state_count: usize,
    /// Number of WFST actions.
    pub wfst_action_count: usize,
}

/// Status of an optimization in the report.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OptimizationStatus {
    /// Automatically applied when the gate is enabled — no user action needed.
    Auto,
    /// Diagnostic only — results are reported but no codegen changes are made.
    Diagnostic,
}

impl Optimization {
    /// Whether this optimization is auto-applied (controls codegen) or
    /// diagnostic-only (info messages).
    pub fn status(&self) -> OptimizationStatus {
        match self {
            // Auto-applied: gate is checked in codegen paths
            Self::LeftFactoring        // A1: write_nfa_merged_prefix_arm left-factoring
            | Self::HotColdSplitting   // A2: dispatch hot/cold splitting
            | Self::MultiTokenLookahead // B1: NFA multi-token dispatch
            | Self::SpilloverPruning   // F1: beam-based spill filter
            | Self::EarlyTermination   // F2: deterministic NFA early exit
            | Self::LazySpillover      // F3: weight-gated spillover
            | Self::WfstMinimization   // B3: cascade gating
            | Self::EnhancedDeadCodeElimination // A4: dead-rule codegen suppression
            | Self::AdaptiveRecovery   // B2: adaptive recovery weight expr
            | Self::BacktrackingElimination // G1: FIRST-set backtracking elimination
            => OptimizationStatus::Auto,

            // Auto-applied (Sprint 6): ContextWeight narrowing in NFA try-all
            | Self::ContextDisambiguation // H1: powerset WFST candidate narrowing
            => OptimizationStatus::Auto,

            // Diagnostic: info messages only, no codegen effect
            Self::AmbiguityTargeting   // A5: per-token ambiguity report
            | Self::WpdsReachabilityCheck // G25: WPDS stack-aware dead-rule verification
            | Self::TrsConfluenceCheck    // T01: Knuth-Bendix critical pair analysis
            | Self::VpaInclusionCheck     // V01: VPA structured sublanguage check
            | Self::SafetyVerification    // S01: WPDS prestar safety check
            | Self::CegarRefinement       // S03: CEGAR refinement loop
            | Self::PetriDeadlockCheck    // N01: Petri net coverability
            => OptimizationStatus::Diagnostic,
        }
    }
}

impl fmt::Display for OptimizationStatus {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Auto => write!(f, "auto"),
            Self::Diagnostic => write!(f, "diag"),
        }
    }
}

/// D2: Unified grammar complexity report.
///
/// Combines per-category metrics, cross-category coupling, WFST analysis,
/// and optimization recommendations into a single structured report.
/// Suitable for output as formatted text or structured JSON for CI integration.
#[derive(Debug, Clone)]
pub struct GrammarComplexityReport {
    /// Grammar name.
    pub grammar_name: String,
    /// Overall grammar profile.
    pub profile: GrammarProfile,
    /// Per-category complexity metrics.
    pub categories: Vec<CategoryComplexity>,
    /// Recommended optimizations: (name, speedup, cost, reason, status).
    pub recommended_optimizations: Vec<(String, f64, f64, String, OptimizationStatus)>,
    /// Total number of WFST states across all categories.
    pub total_wfst_states: usize,
    /// Total number of WFST transitions across all categories.
    pub total_wfst_transitions: usize,
    /// Number of entries in the composed dispatch weight map.
    /// Covers all `(category, token)` pairs with resolved weights.
    pub composed_dispatch_entries: usize,
    /// Number of ambiguities resolved deterministically by composed dispatch.
    /// These are tokens where the lexer×parser composition picks a unique winner.
    pub resolved_ambiguities: usize,
}

impl GrammarComplexityReport {
    /// D2: Build a complexity report from pipeline data.
    ///
    /// `composed_dispatch_entries`: total entries in the composed weight map.
    /// `resolved_ambiguities`: number of ambiguous tokens resolved by composition.
    pub fn build(
        grammar_name: &str,
        profile: &GrammarProfile,
        prediction_wfsts: &HashMap<String, PredictionWfst>,
        first_sets: &HashMap<String, FirstSet>,
        composed_dispatch_entries: usize,
        resolved_ambiguities: usize,
    ) -> Self {
        let mut categories = Vec::with_capacity(prediction_wfsts.len());
        let mut total_transitions = 0usize;
        let mut total_states = 0usize;

        for (cat_name, wfst) in prediction_wfsts {
            let dispatch_token_count = first_sets
                .get(cat_name)
                .map(|fs| fs.tokens.len())
                .unwrap_or(0);

            let mut ambiguous_count = 0;
            let mut max_ambiguity = 0;
            if let Some(first_set) = first_sets.get(cat_name) {
                for token in &first_set.tokens {
                    let predictions = wfst.predict(token);
                    if predictions.len() > 1 {
                        ambiguous_count += 1;
                        max_ambiguity = max_ambiguity.max(predictions.len());
                    }
                }
            }

            let state_count = wfst.num_states();
            let action_count = wfst.num_actions();
            total_states += state_count;
            total_transitions += wfst.states.iter().map(|s| s.transitions.len()).sum::<usize>();

            categories.push(CategoryComplexity {
                name: cat_name.clone(),
                dispatch_token_count,
                ambiguous_token_count: ambiguous_count,
                max_ambiguity,
                wfst_state_count: state_count,
                wfst_action_count: action_count,
            });
        }

        // Sort categories by name for deterministic output
        categories.sort_by(|a, b| a.name.cmp(&b.name));

        let recommended = recommended_optimizations(profile);
        let recommended_optimizations = recommended
            .iter()
            .map(|c| {
                (
                    format!("{:?}", c.optimization),
                    c.speedup.value(),
                    c.compile_cost.value(),
                    c.reason.clone(),
                    c.optimization.status(),
                )
            })
            .collect();

        GrammarComplexityReport {
            grammar_name: grammar_name.to_string(),
            profile: profile.clone(),
            categories,
            recommended_optimizations,
            total_wfst_states: total_states,
            total_wfst_transitions: total_transitions,
            composed_dispatch_entries,
            resolved_ambiguities,
        }
    }

    /// D2: Format as a compact single-line summary with optional per-category detail.
    pub fn format_compact(&self) -> String {
        use std::fmt::Write;
        let mut out = String::new();

        // Line 1: key scalar metrics
        write!(
            out,
            "{} cats, {} rules, {} WFST states, {} transitions, {:.1}% ambiguous, {:.1}% cold, {} NFA spill, {} dispatch entries ({} resolved)",
            self.profile.category_count,
            self.profile.rule_count,
            self.total_wfst_states,
            self.total_wfst_transitions,
            self.profile.ambiguous_fraction * 100.0,
            self.profile.cold_fraction * 100.0,
            self.profile.nfa_spillover_categories,
            self.composed_dispatch_entries,
            self.resolved_ambiguities,
        ).unwrap();

        // Line 2: per-category summary (only if ≤ 8 categories)
        if !self.categories.is_empty() && self.categories.len() <= 8 {
            let cat_parts: Vec<String> = self.categories.iter()
                .map(|c| format!("{}({}t/{}a)", c.name, c.dispatch_token_count, c.wfst_action_count))
                .collect();
            write!(out, "\n  per-category: {}", cat_parts.join(" ")).unwrap();
        }

        out
    }

    /// D2: Convert to a lint diagnostic for consistent emission.
    pub fn to_diagnostic(&self) -> crate::lint::LintDiagnostic {
        crate::lint::LintDiagnostic {
            id: "D02",
            name: "grammar-profile",
            severity: crate::lint::LintSeverity::Note,
            category: None,
            rule: None,
            message: self.format_compact(),
            hint: None,
            grammar_name: Some(self.grammar_name.clone()),
            source_location: None,
        }
    }

    /// D2: Format as a human-readable table (legacy, kept for backward compatibility).
    pub fn format_table(&self) -> String {
        self.format_compact()
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    fn simple_profile() -> GrammarProfile {
        GrammarProfile {
            shared_prefix_ratio: 0.0,
            cold_fraction: 0.0,
            ambiguous_fraction: 0.0,
            ambiguous_count: 0,
            category_count: 4,
            rule_count: 20,
            nfa_spillover_categories: 0,
            has_beam_width: false,
            total_wfst_states: 10,
            avg_trie_depth: 0.0,
            ambiguity_score: 0.0,
            deterministic_ratio: 1.0,
        }
    }

    #[test]
    fn test_simple_grammar_few_optimizations() {
        let profile = simple_profile();
        let recommended = recommended_optimizations(&profile);
        // Simple grammar: B2 (adaptive recovery) and A4 (DCE) should be recommended
        let names: Vec<_> = recommended.iter().map(|c| c.optimization).collect();
        assert!(
            names.contains(&Optimization::AdaptiveRecovery),
            "adaptive recovery should always be recommended"
        );
        assert!(
            names.contains(&Optimization::EnhancedDeadCodeElimination),
            "DCE should be recommended for grammars with >5 rules"
        );
    }

    #[test]
    fn test_ambiguous_grammar_enables_lookahead() {
        let profile = GrammarProfile {
            ambiguous_fraction: 0.25,
            ambiguous_count: 3,
            ..simple_profile()
        };
        let recommended = recommended_optimizations(&profile);
        let names: Vec<_> = recommended.iter().map(|c| c.optimization).collect();
        assert!(
            names.contains(&Optimization::MultiTokenLookahead),
            "multi-token lookahead should be recommended for ambiguous grammars: {:?}",
            names
        );
        assert!(
            names.contains(&Optimization::AmbiguityTargeting),
            "ambiguity targeting should be recommended: {:?}",
            names
        );
    }

    #[test]
    fn test_cold_heavy_grammar() {
        let profile = GrammarProfile {
            cold_fraction: 0.6,
            ..simple_profile()
        };
        let recommended = recommended_optimizations(&profile);
        let names: Vec<_> = recommended.iter().map(|c| c.optimization).collect();
        assert!(
            names.contains(&Optimization::HotColdSplitting),
            "hot/cold splitting should be recommended when cold_fraction > 0.4: {:?}",
            names
        );
    }

    #[test]
    fn test_spillover_with_beam() {
        let profile = GrammarProfile {
            nfa_spillover_categories: 2,
            has_beam_width: true,
            ..simple_profile()
        };
        let recommended = recommended_optimizations(&profile);
        let names: Vec<_> = recommended.iter().map(|c| c.optimization).collect();
        assert!(
            names.contains(&Optimization::SpilloverPruning),
            "spillover pruning should be recommended when beam is set: {:?}",
            names
        );
        assert!(
            names.contains(&Optimization::LazySpillover),
            "lazy spillover should be recommended when spillover categories exist: {:?}",
            names
        );
    }

    #[test]
    fn test_lexicographic_ordering() {
        // Verify that among candidates with equal speedup, cheaper ones come first
        let a = OptimizationCandidate::new(
            Optimization::LeftFactoring,
            0.5,
            1.0,
            true,
            "test".to_string(),
        );
        let b = OptimizationCandidate::new(
            Optimization::HotColdSplitting,
            0.5,
            0.05,
            true,
            "test".to_string(),
        );
        assert!(
            b.score < a.score,
            "cheaper compile cost should rank better when speedup is equal"
        );
    }

    #[test]
    fn test_all_candidates_evaluated() {
        let profile = simple_profile();
        let all = evaluate_optimizations(&profile);
        assert_eq!(all.len(), 18, "should evaluate all 18 optimization candidates");
    }

    #[test]
    fn test_ambiguity_targeting_empty() {
        let wfsts = HashMap::new();
        let first_sets = HashMap::new();
        let result = analyze_ambiguity_targets(&wfsts, &first_sets, 1);
        assert!(result.ambiguous_tokens.is_empty());
        assert_eq!(result.unambiguous_count, 0);
        assert_eq!(result.max_ambiguity, 0);
        assert!(result.presized_categories.is_empty());
    }

    #[test]
    fn test_ambiguity_targeting_result_fields() {
        use crate::prediction::DispatchAction;
        use crate::wfst::PredictionWfstBuilder;
        use crate::token_id::TokenIdMap;
        use crate::automata::semiring::TropicalWeight;

        // Build a WFST with one ambiguous token (Ident → 2 rules) and one unambiguous (LParen)
        let token_map = TokenIdMap::from_names(
            vec!["Ident".to_string(), "LParen".to_string()].into_iter(),
        );
        let mut builder = PredictionWfstBuilder::new("Proc", token_map);
        builder.add_action(
            "Ident",
            DispatchAction::Direct {
                rule_label: "PInput".to_string(),
                parse_fn: "parse_pinput".to_string(),
            },
            TropicalWeight::new(0.0),
        );
        builder.add_action(
            "Ident",
            DispatchAction::Direct {
                rule_label: "POutput".to_string(),
                parse_fn: "parse_poutput".to_string(),
            },
            TropicalWeight::new(0.5),
        );
        builder.add_action(
            "LParen",
            DispatchAction::Direct {
                rule_label: "PSend".to_string(),
                parse_fn: "parse_psend".to_string(),
            },
            TropicalWeight::new(0.0),
        );
        let wfst = builder.build();

        let mut first_set = FirstSet::new();
        first_set.tokens.insert("Ident".to_string());
        first_set.tokens.insert("LParen".to_string());

        let mut wfsts = HashMap::new();
        wfsts.insert("Proc".to_string(), wfst);
        let mut fsets = HashMap::new();
        fsets.insert("Proc".to_string(), first_set);

        let result = analyze_ambiguity_targets(&wfsts, &fsets, 1);

        // One ambiguous token (Ident with 2 alternatives), one unambiguous (LParen)
        assert_eq!(result.ambiguous_tokens.len(), 1);
        assert_eq!(result.unambiguous_count, 1);
        assert_eq!(result.max_ambiguity, 2);

        let ident_info = &result.ambiguous_tokens[0];
        assert_eq!(ident_info.category, "Proc");
        assert_eq!(ident_info.token, "Ident");
        assert_eq!(ident_info.alternative_count, 2);
        assert_eq!(ident_info.rule_labels.len(), 2);
        assert!(ident_info.lookahead_candidate); // count=2 > threshold=1

        // Pre-sizing: Proc category should have max_ambiguity-1 = 1
        assert_eq!(result.presized_categories.len(), 1);
        let (cat, size) = &result.presized_categories[0];
        assert_eq!(cat, "Proc");
        assert_eq!(*size, 1); // 2-1 = 1 alternative spilled
    }

    #[test]
    fn test_f2_requires_no_spillover() {
        // F2 with spillover categories — should NOT be recommended
        let profile = GrammarProfile {
            nfa_spillover_categories: 1,
            ambiguous_count: 2,
            ..simple_profile()
        };
        let recommended = recommended_optimizations(&profile);
        let names: Vec<_> = recommended.iter().map(|c| c.optimization).collect();
        assert!(
            !names.contains(&Optimization::EarlyTermination),
            "F2 should not be recommended when NFA spillover is needed: {:?}",
            names
        );
    }

    // ── A3: OptimizationGates tests ──────────────────────────────────────

    #[test]
    fn test_all_enabled_gates() {
        let gates = OptimizationGates::all_enabled();
        assert!(gates.left_factoring);
        assert!(gates.hot_cold_splitting);
        assert!(gates.multi_token_lookahead);
        assert!(gates.spillover_pruning);
        assert!(gates.early_termination);
        assert!(gates.lazy_spillover);
        assert!(gates.wfst_minimization);
        assert!(gates.enhanced_dce);
        assert!(gates.ambiguity_targeting);
        assert!(gates.adaptive_recovery);
    }

    #[test]
    fn test_gates_from_simple_grammar() {
        // Simple grammar: only B2 (adaptive recovery) and A4 (DCE) recommended
        let profile = simple_profile();
        let recommended = recommended_optimizations(&profile);
        let gates = OptimizationGates::from_recommendations(&recommended);
        assert!(
            gates.adaptive_recovery,
            "B2 should be enabled for simple grammars"
        );
        assert!(
            gates.enhanced_dce,
            "A4 should be enabled for grammars with >5 rules"
        );
        // All other gates should be disabled for a simple grammar
        assert!(
            !gates.left_factoring,
            "A1 should not be enabled: shared_prefix_ratio=0.0"
        );
        assert!(
            !gates.hot_cold_splitting,
            "A2 should not be enabled: cold_fraction=0.0"
        );
        assert!(
            !gates.multi_token_lookahead,
            "B1 should not be enabled: ambiguous_fraction=0.0"
        );
    }

    #[test]
    fn test_gates_from_ambiguous_grammar() {
        let profile = GrammarProfile {
            ambiguous_fraction: 0.25,
            ambiguous_count: 3,
            nfa_spillover_categories: 2,
            has_beam_width: true,
            ..simple_profile()
        };
        let recommended = recommended_optimizations(&profile);
        let gates = OptimizationGates::from_recommendations(&recommended);
        assert!(gates.multi_token_lookahead, "B1 should be enabled for ambiguous grammars");
        assert!(gates.ambiguity_targeting, "A5 should be enabled");
        assert!(gates.spillover_pruning, "F1 should be enabled with beam + spillover");
        assert!(gates.lazy_spillover, "F3 should be enabled with spillover categories");
        // F2 should NOT be enabled when spillover categories exist
        assert!(
            !gates.early_termination,
            "F2 should not be enabled when NFA spillover is needed"
        );
    }

    #[test]
    fn test_gates_from_cold_heavy_grammar() {
        let profile = GrammarProfile {
            cold_fraction: 0.6,
            ..simple_profile()
        };
        let recommended = recommended_optimizations(&profile);
        let gates = OptimizationGates::from_recommendations(&recommended);
        assert!(
            gates.hot_cold_splitting,
            "A2 should be enabled when cold_fraction > 0.4"
        );
    }

    #[test]
    fn test_gates_from_large_wfst_grammar() {
        let profile = GrammarProfile {
            total_wfst_states: 50,
            ..simple_profile()
        };
        let recommended = recommended_optimizations(&profile);
        let gates = OptimizationGates::from_recommendations(&recommended);
        assert!(
            gates.wfst_minimization,
            "B3 should be enabled when total_wfst_states > 4"
        );
    }

    // ── D2: GrammarComplexityReport tests ──────────────────────────────

    #[test]
    fn test_d2_report_build_empty() {
        let profile = simple_profile();
        let wfsts = HashMap::new();
        let first_sets = HashMap::new();
        let report = GrammarComplexityReport::build("empty", &profile, &wfsts, &first_sets, 0, 0);
        assert_eq!(report.grammar_name, "empty");
        assert!(report.categories.is_empty());
        assert_eq!(report.total_wfst_states, 0);
        assert_eq!(report.total_wfst_transitions, 0);
    }

    #[test]
    fn test_d2_report_build_with_wfst() {
        use crate::prediction::DispatchAction;
        use crate::wfst::PredictionWfstBuilder;
        use crate::token_id::TokenIdMap;
        use crate::automata::semiring::TropicalWeight;

        let token_map = TokenIdMap::from_names(
            vec!["Ident".to_string(), "LParen".to_string()].into_iter(),
        );
        let mut builder = PredictionWfstBuilder::new("Proc", token_map);
        builder.add_action(
            "Ident",
            DispatchAction::Direct {
                rule_label: "PInput".to_string(),
                parse_fn: "parse_pinput".to_string(),
            },
            TropicalWeight::new(0.0),
        );
        builder.add_action(
            "Ident",
            DispatchAction::Direct {
                rule_label: "POutput".to_string(),
                parse_fn: "parse_poutput".to_string(),
            },
            TropicalWeight::new(0.5),
        );
        builder.add_action(
            "LParen",
            DispatchAction::Direct {
                rule_label: "PSend".to_string(),
                parse_fn: "parse_psend".to_string(),
            },
            TropicalWeight::new(0.0),
        );
        let wfst = builder.build();

        let mut first_set = FirstSet::new();
        first_set.tokens.insert("Ident".to_string());
        first_set.tokens.insert("LParen".to_string());

        let mut wfsts = HashMap::new();
        wfsts.insert("Proc".to_string(), wfst);
        let mut fsets = HashMap::new();
        fsets.insert("Proc".to_string(), first_set);

        let profile = GrammarProfile {
            category_count: 1,
            rule_count: 3,
            ..simple_profile()
        };

        let report = GrammarComplexityReport::build("test_lang", &profile, &wfsts, &fsets, 0, 0);
        assert_eq!(report.grammar_name, "test_lang");
        assert_eq!(report.categories.len(), 1);

        let cat = &report.categories[0];
        assert_eq!(cat.name, "Proc");
        assert_eq!(cat.dispatch_token_count, 2);
        assert_eq!(cat.ambiguous_token_count, 1); // Ident is ambiguous
        assert_eq!(cat.max_ambiguity, 2); // Ident has 2 alternatives
        assert!(cat.wfst_state_count > 0);
        assert_eq!(cat.wfst_action_count, 3);
        assert!(report.total_wfst_states > 0);
        assert!(report.total_wfst_transitions > 0);
    }

    #[test]
    fn test_d2_report_categories_sorted_by_name() {
        use crate::prediction::DispatchAction;
        use crate::wfst::PredictionWfstBuilder;
        use crate::token_id::TokenIdMap;
        use crate::automata::semiring::TropicalWeight;

        // Create two categories: "Proc" and "Int" — report should sort alphabetically
        let mut wfsts = HashMap::new();
        let mut fsets = HashMap::new();

        for cat_name in &["Proc", "Int"] {
            let token_map = TokenIdMap::from_names(
                vec!["Ident".to_string()].into_iter(),
            );
            let mut builder = PredictionWfstBuilder::new(cat_name, token_map);
            builder.add_action(
                "Ident",
                DispatchAction::Direct {
                    rule_label: format!("{}_rule", cat_name),
                    parse_fn: format!("parse_{}", cat_name.to_lowercase()),
                },
                TropicalWeight::new(0.0),
            );
            wfsts.insert(cat_name.to_string(), builder.build());
            let mut fs = FirstSet::new();
            fs.tokens.insert("Ident".to_string());
            fsets.insert(cat_name.to_string(), fs);
        }

        let profile = GrammarProfile {
            category_count: 2,
            ..simple_profile()
        };
        let report = GrammarComplexityReport::build("multi", &profile, &wfsts, &fsets, 0, 0);
        assert_eq!(report.categories.len(), 2);
        assert_eq!(report.categories[0].name, "Int"); // Int before Proc alphabetically
        assert_eq!(report.categories[1].name, "Proc");
    }

    #[test]
    fn test_d2_format_compact_contains_key_metrics() {
        let profile = GrammarProfile {
            ambiguous_fraction: 0.15,
            cold_fraction: 0.3,
            nfa_spillover_categories: 1,
            ..simple_profile()
        };
        let report = GrammarComplexityReport {
            grammar_name: "TestLang".to_string(),
            profile: profile.clone(),
            categories: vec![CategoryComplexity {
                name: "Expr".to_string(),
                dispatch_token_count: 5,
                ambiguous_token_count: 2,
                max_ambiguity: 3,
                wfst_state_count: 8,
                wfst_action_count: 10,
            }],
            recommended_optimizations: vec![
                ("AmbiguityTargeting".to_string(), 1.9, 0.1, "ambiguous_fraction=0.15".to_string(), OptimizationStatus::Diagnostic),
            ],
            total_wfst_states: 8,
            total_wfst_transitions: 12,
            composed_dispatch_entries: 7,
            resolved_ambiguities: 2,
        };

        let compact = report.format_compact();
        assert!(compact.contains("4 cats"), "should contain category count");
        assert!(compact.contains("20 rules"), "should contain rule count");
        assert!(compact.contains("8 WFST states"), "should contain WFST state count");
        assert!(compact.contains("12 transitions"), "should contain transition count");
        assert!(compact.contains("15.0% ambiguous"), "should contain ambiguous fraction");
        assert!(compact.contains("30.0% cold"), "should contain cold fraction");
        assert!(compact.contains("1 NFA spill"), "should contain NFA spillover count");
        assert!(compact.contains("7 dispatch entries"), "should contain dispatch entries");
        assert!(compact.contains("2 resolved"), "should contain resolved count");
        assert!(compact.contains("Expr(5t/10a)"), "should contain per-category summary");
        // Recommendations are NOT in compact format (I05 lint handles them)
        assert!(!compact.contains("AmbiguityTargeting"), "recommendations should not appear in compact format");
    }

    #[test]
    fn test_d2_format_compact_empty_categories() {
        let profile = simple_profile();
        let report = GrammarComplexityReport {
            grammar_name: "Simple".to_string(),
            profile,
            categories: vec![],
            recommended_optimizations: vec![],
            total_wfst_states: 0,
            total_wfst_transitions: 0,
            composed_dispatch_entries: 0,
            resolved_ambiguities: 0,
        };
        let compact = report.format_compact();
        // Should NOT contain per-category line when no categories
        assert!(!compact.contains("per-category"), "empty categories should not show per-category line");
        // Should still contain scalar metrics
        assert!(compact.contains("4 cats"), "should contain category count");
        assert!(compact.contains("20 rules"), "should contain rule count");
    }

    #[test]
    fn test_d2_to_diagnostic() {
        let profile = simple_profile();
        let report = GrammarComplexityReport {
            grammar_name: "TestLang".to_string(),
            profile,
            categories: vec![],
            recommended_optimizations: vec![],
            total_wfst_states: 0,
            total_wfst_transitions: 0,
            composed_dispatch_entries: 0,
            resolved_ambiguities: 0,
        };
        let diag = report.to_diagnostic();
        assert_eq!(diag.id, "D02");
        assert_eq!(diag.name, "grammar-profile");
        assert_eq!(diag.grammar_name.as_deref(), Some("TestLang"));
        assert!(matches!(diag.severity, crate::lint::LintSeverity::Note));
    }

    #[test]
    fn test_d2_report_includes_recommendations() {
        use crate::prediction::DispatchAction;
        use crate::wfst::PredictionWfstBuilder;
        use crate::token_id::TokenIdMap;
        use crate::automata::semiring::TropicalWeight;

        // Build a grammar profile that triggers B2 (adaptive recovery) + A4 (DCE)
        let token_map = TokenIdMap::from_names(
            vec!["Ident".to_string()].into_iter(),
        );
        let mut builder = PredictionWfstBuilder::new("Proc", token_map);
        builder.add_action(
            "Ident",
            DispatchAction::Direct {
                rule_label: "PInput".to_string(),
                parse_fn: "parse_pinput".to_string(),
            },
            TropicalWeight::new(0.0),
        );
        let wfst = builder.build();

        let mut wfsts = HashMap::new();
        wfsts.insert("Proc".to_string(), wfst);
        let mut fsets = HashMap::new();
        let mut fs = FirstSet::new();
        fs.tokens.insert("Ident".to_string());
        fsets.insert("Proc".to_string(), fs);

        let profile = simple_profile(); // rule_count=20 > 5 → A4 applicable
        let report = GrammarComplexityReport::build("reco_test", &profile, &wfsts, &fsets, 0, 0);

        // Should have at least B2 (adaptive recovery) and A4 (DCE) in recommendations
        assert!(
            !report.recommended_optimizations.is_empty(),
            "should have at least one recommendation"
        );
        let opt_names: Vec<&str> = report.recommended_optimizations.iter()
            .map(|(name, _, _, _, _)| name.as_str())
            .collect();
        assert!(
            opt_names.iter().any(|n| n.contains("AdaptiveRecovery")),
            "B2 should be recommended: {:?}",
            opt_names
        );

        // Verify status tags in report: B2 (AdaptiveRecovery) should be auto
        let statuses: Vec<(&str, &OptimizationStatus)> = report.recommended_optimizations.iter()
            .map(|(name, _, _, _, status)| (name.as_str(), status))
            .collect();
        assert!(
            statuses.iter().any(|(n, s)| n.contains("AdaptiveRecovery") && **s == OptimizationStatus::Auto),
            "B2 should have Auto status: {:?}", statuses
        );
    }

    // ══════════════════════════════════════════════════════════════════
    // Sprint 4: FromStr, none_enabled, from_env, from_env_or_recommendations
    // ══════════════════════════════════════════════════════════════════

    #[test]
    fn test_optimization_from_str_short_codes() {
        use std::str::FromStr;
        assert_eq!(Optimization::from_str("A1").expect("A1"), Optimization::LeftFactoring);
        assert_eq!(Optimization::from_str("A2").expect("A2"), Optimization::HotColdSplitting);
        assert_eq!(Optimization::from_str("A4").expect("A4"), Optimization::EnhancedDeadCodeElimination);
        assert_eq!(Optimization::from_str("A5").expect("A5"), Optimization::AmbiguityTargeting);
        assert_eq!(Optimization::from_str("B1").expect("B1"), Optimization::MultiTokenLookahead);
        assert_eq!(Optimization::from_str("B2").expect("B2"), Optimization::AdaptiveRecovery);
        assert_eq!(Optimization::from_str("B3").expect("B3"), Optimization::WfstMinimization);
        assert_eq!(Optimization::from_str("F1").expect("F1"), Optimization::SpilloverPruning);
        assert_eq!(Optimization::from_str("F2").expect("F2"), Optimization::EarlyTermination);
        assert_eq!(Optimization::from_str("F3").expect("F3"), Optimization::LazySpillover);
    }

    #[test]
    fn test_optimization_from_str_full_names() {
        use std::str::FromStr;
        assert_eq!(Optimization::from_str("LeftFactoring").expect("name"), Optimization::LeftFactoring);
        assert_eq!(Optimization::from_str("adaptiverecovery").expect("lower"), Optimization::AdaptiveRecovery);
        assert_eq!(Optimization::from_str("LAZYSPILLOVER").expect("upper"), Optimization::LazySpillover);
        assert_eq!(Optimization::from_str("EnhancedDCE").expect("alias"), Optimization::EnhancedDeadCodeElimination);
    }

    #[test]
    fn test_optimization_from_str_display_format() {
        use std::str::FromStr;
        assert_eq!(Optimization::from_str("A1:LeftFactoring").expect("display"), Optimization::LeftFactoring);
        assert_eq!(Optimization::from_str("B2:AdaptiveRecovery").expect("display"), Optimization::AdaptiveRecovery);
    }

    #[test]
    fn test_optimization_from_str_invalid() {
        use std::str::FromStr;
        assert!(Optimization::from_str("bogus").is_err());
        assert!(Optimization::from_str("X9").is_err());
        assert!(Optimization::from_str("A3").is_err()); // A3 does not exist
    }

    #[test]
    fn test_none_enabled_all_false() {
        let gates = OptimizationGates::none_enabled();
        assert!(!gates.left_factoring);
        assert!(!gates.hot_cold_splitting);
        assert!(!gates.multi_token_lookahead);
        assert!(!gates.spillover_pruning);
        assert!(!gates.early_termination);
        assert!(!gates.lazy_spillover);
        assert!(!gates.wfst_minimization);
        assert!(!gates.enhanced_dce);
        assert!(!gates.ambiguity_targeting);
        assert!(!gates.adaptive_recovery);
    }

    #[test]
    fn test_from_env_with_specific_opts() {
        // Set env var to enable only A1 and F3
        std::env::set_var("PRATTAIL_AUTO_OPTIMIZE", "A1,F3");
        let result = OptimizationGates::from_env();
        // Clean up before asserting (env is process-global)
        std::env::remove_var("PRATTAIL_AUTO_OPTIMIZE");

        let gates = result.expect("parse").expect("should be Some");
        assert!(gates.left_factoring, "A1 should be enabled");
        assert!(gates.lazy_spillover, "F3 should be enabled");
        assert!(!gates.hot_cold_splitting, "A2 should not be enabled");
        assert!(!gates.adaptive_recovery, "B2 should not be enabled");
        assert!(!gates.enhanced_dce, "A4 should not be enabled");
    }

    #[test]
    fn test_from_env_all() {
        std::env::set_var("PRATTAIL_AUTO_OPTIMIZE", "all");
        let result = OptimizationGates::from_env();
        std::env::remove_var("PRATTAIL_AUTO_OPTIMIZE");

        let gates = result.expect("parse").expect("should be Some");
        assert!(gates.left_factoring);
        assert!(gates.hot_cold_splitting);
        assert!(gates.multi_token_lookahead);
        assert!(gates.spillover_pruning);
        assert!(gates.early_termination);
        assert!(gates.lazy_spillover);
        assert!(gates.wfst_minimization);
        assert!(gates.enhanced_dce);
        assert!(gates.ambiguity_targeting);
        assert!(gates.adaptive_recovery);
        assert!(gates.backtracking_elimination);
    }

    #[test]
    fn test_from_env_none() {
        std::env::set_var("PRATTAIL_AUTO_OPTIMIZE", "none");
        let result = OptimizationGates::from_env();
        std::env::remove_var("PRATTAIL_AUTO_OPTIMIZE");

        let gates = result.expect("parse").expect("should be Some");
        assert!(!gates.left_factoring);
        assert!(!gates.adaptive_recovery);
        assert!(!gates.backtracking_elimination);
    }

    #[test]
    fn test_from_env_unset() {
        std::env::remove_var("PRATTAIL_AUTO_OPTIMIZE");
        let result = OptimizationGates::from_env();
        assert!(result.expect("no error").is_none(), "unset should return None");
    }

    #[test]
    fn test_from_env_invalid_value() {
        std::env::set_var("PRATTAIL_AUTO_OPTIMIZE", "A1,bogus,F3");
        let result = OptimizationGates::from_env();
        std::env::remove_var("PRATTAIL_AUTO_OPTIMIZE");

        assert!(result.is_err(), "should fail on invalid optimization name");
    }

    #[test]
    fn test_from_env_or_recommendations_fallback() {
        // Ensure env var is unset so it falls back to recommendations
        std::env::remove_var("PRATTAIL_AUTO_OPTIMIZE");
        let profile = GrammarProfile {
            rule_count: 20,
            ..simple_profile()
        };
        let recommended = recommended_optimizations(&profile);
        let gates = OptimizationGates::from_env_or_recommendations(&recommended);
        // Should be identical to from_recommendations
        let expected = OptimizationGates::from_recommendations(&recommended);
        assert_eq!(gates.left_factoring, expected.left_factoring);
        assert_eq!(gates.adaptive_recovery, expected.adaptive_recovery);
        assert_eq!(gates.enhanced_dce, expected.enhanced_dce);
    }

    #[test]
    fn test_trs_confluence_check_evaluated() {
        let profile = simple_profile();
        let all = evaluate_optimizations(&profile);
        assert!(
            all.iter().any(|c| c.optimization == Optimization::TrsConfluenceCheck),
            "TrsConfluenceCheck should be in evaluated candidates"
        );
    }

    #[test]
    fn test_vpa_inclusion_check_evaluated() {
        let profile = simple_profile();
        let all = evaluate_optimizations(&profile);
        assert!(
            all.iter().any(|c| c.optimization == Optimization::VpaInclusionCheck),
            "VpaInclusionCheck should be in evaluated candidates"
        );
    }

    #[test]
    fn test_safety_verification_evaluated() {
        let profile = simple_profile();
        let all = evaluate_optimizations(&profile);
        assert!(
            all.iter().any(|c| c.optimization == Optimization::SafetyVerification),
            "SafetyVerification should be in evaluated candidates"
        );
    }

    #[test]
    fn test_cegar_refinement_evaluated() {
        let profile = simple_profile();
        let all = evaluate_optimizations(&profile);
        assert!(
            all.iter().any(|c| c.optimization == Optimization::CegarRefinement),
            "CegarRefinement should be in evaluated candidates"
        );
    }

    #[test]
    fn test_petri_deadlock_check_evaluated() {
        let profile = simple_profile();
        let all = evaluate_optimizations(&profile);
        assert!(
            all.iter().any(|c| c.optimization == Optimization::PetriDeadlockCheck),
            "PetriDeadlockCheck should be in evaluated candidates"
        );
    }
}
