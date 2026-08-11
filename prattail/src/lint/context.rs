use super::*;

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
    /// Labels intentionally excluded from parser-root dead-rule diagnostics.
    pub dead_rule_ignore_labels: &'a HashSet<String>,
    /// Declared refinement types; G08 and related cast-graph lints treat
    /// refinement categories separately from ordinary cast-connected categories.
    pub refinement_types: &'a [crate::RefinementTypeSpec],
    /// Grammar profile for severity modulation.
    pub grammar_profile: Option<&'a crate::cost_benefit::GrammarProfile>,
    /// WPDS analysis results (stack-aware reachability).
    /// `None` if WPDS analysis was not run (G25 gate disabled or < 2 categories).
    pub wpds_analysis: Option<&'a crate::wpds::WpdsAnalysis>,
    /// P05: Wall-clock time spent in WPDS analysis (set by pipeline).
    pub wpds_elapsed: Option<std::time::Duration>,

    // ── Mathematical analysis results ──────────────────────────────────────
    /// Safety verification result (always-on when WPDS runs).
    pub safety_result:
        Option<&'a crate::verify::SafetyResult<crate::automata::semiring::BooleanWeight>>,
    /// CEGAR verification result (always-on when WPDS runs).
    pub cegar_result: Option<&'a crate::cegar::CegarLog>,
    /// Algebraic program analysis (Tarjan path expressions).
    pub algebraic_result: Option<&'a crate::algebraic::AlgebraicSummary>,
    /// P06: Wall-clock time spent in mathematical analysis phase.
    pub math_analysis_elapsed: Option<std::time::Duration>,

    /// Confluence analysis (TRS critical pairs).
    pub confluence_result: Option<&'a crate::confluence::ConfluenceAnalysis>,
    /// Termination analysis (dependency pairs).
    pub termination_result: Option<&'a crate::termination::TerminationResult>,
    /// VPA analysis (structured sublanguage).
    pub vpa_result: Option<&'a crate::vpa::VpaAnalysis>,
    /// Weighted tree automaton analysis.
    pub wta_result: Option<&'a crate::tree_automaton::WtaAnalysis>,
    /// EWPDS merge site analysis.
    pub ewpds_result: Option<&'a crate::ewpds::EwpdsAnalysis>,
    /// ARA affine-relation analysis.
    pub ara_result: Option<&'a crate::ara::AraAnalysis>,
    /// Petri net analysis.
    pub petri_result: Option<&'a crate::petri::PetriAnalysis>,
    /// Nominal automaton analysis.
    pub nominal_result: Option<&'a crate::nominal::NominalAnalysis>,
    /// Alternating automaton analysis.
    pub alternating_result: Option<&'a crate::alternating::AlternatingAnalysis>,
    /// LTL model checking results.
    pub ltl_results: Option<&'a Vec<crate::ltl::LtlCheckResult>>,
    /// Provenance tracking results.
    pub provenance_result: Option<&'a crate::provenance::ProvenanceAnalysis>,
    /// Cost register automaton analysis.
    pub cra_result: Option<&'a crate::cra::CraAnalysis>,
    /// Theory morphism check.
    pub morphism_result: Option<&'a crate::morphism::MorphismCheck>,
    /// KAT check (Hoare triples, equivalences).
    pub kat_result: Option<&'a crate::kat::KatCheck>,

    // ── Advanced automata analysis results ──────────────────────────────────
    /// Symbolic automata guard analysis.
    pub symbolic_result: Option<&'a crate::symbolic::SymbolicAnalysis>,
    /// Weighted Büchi automaton analysis.
    pub buchi_result: Option<&'a crate::buchi::BuchiAnalysis>,
    /// Weighted MSO logic analysis.
    pub mso_result: Option<&'a crate::weighted_mso::MsoAnalysis>,
    /// Probabilistic automaton analysis.
    pub probabilistic_result: Option<&'a crate::probabilistic::ProbabilisticAnalysis>,
    /// Register automaton analysis.
    pub register_result: Option<&'a crate::register_automata::RegisterAnalysis>,
    /// Parity tree automaton analysis.
    pub parity_tree_result: Option<&'a crate::parity_tree::ParityTreeAnalysis>,
    /// Multi-tape automaton analysis.
    pub multi_tape_result: Option<&'a crate::multi_tape::MultiTapeAnalysis>,
    /// Multiset automaton analysis.
    pub multiset_result: Option<&'a crate::multiset_automata::MultisetAnalysisResult>,
    /// Two-way transducer analysis.
    pub two_way_result: Option<&'a crate::two_way_transducer::TwoWayAnalysis>,
    /// Symbolic finite transducer analysis.
    pub sft_result: Option<&'a crate::sft::SftAnalysis>,
    /// E-graph equality saturation analysis.
    pub egraph_result: Option<&'a crate::egraph::EGraphAnalysis>,
    /// Predicate dispatch diagnostics.
    pub dispatch_diagnostics: Option<&'a crate::predicate_dispatch::DispatchDiagnostics>,

    // ── Constraint theory analysis results ──────────────────────────────────
    /// Presburger arithmetic guard analysis results.
    pub presburger_result: Option<&'a crate::presburger::PresburgerAnalysis>,
    /// Structural unification guard analysis results.
    pub unification_result: Option<&'a crate::unification::UnificationAnalysis>,
    /// Subtype lattice guard analysis results.
    pub lattice_result: Option<&'a crate::lattice_theory::LatticeAnalysis>,

    // ── Refinement type analysis results ─────────────────────────────────
    /// Refinement type analysis (satisfiability, subtyping, decidability).
    pub refinement_analysis: Option<&'a crate::pipeline::RefinementAnalysisResult>,

    // ── Hindley-Milner base-sort consistency (OSLF Phase 6 `.1`) ──────────
    /// HM constructor-arrow base-sort consistency result; the HM01 lint reads
    /// its `sort_mismatches`.
    pub hindley_result: Option<&'a crate::hindley_milner::HmInferenceAnalysis>,
}

// ══════════════════════════════════════════════════════════════════════════════
// DB04: Cached lint results across builds
// ══════════════════════════════════════════════════════════════════════════════

/// Compute a structural hash of the grammar specification from the lint context.
///
/// The hash covers: grammar name, category count/names, rule count/labels/categories,
/// syntax patterns (serialized), and binding power table entries. Changes to any of
/// these inputs invalidate the cache.
pub fn compute_grammar_hash(ctx: &LintContext) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut hasher = std::hash::DefaultHasher::new();

    // Grammar name
    ctx.grammar_name.hash(&mut hasher);

    // Categories: count, names, primary flag
    ctx.categories.len().hash(&mut hasher);
    for cat in ctx.categories {
        cat.name.hash(&mut hasher);
        cat.is_primary.hash(&mut hasher);
    }

    // Rules: count, labels, categories, first items, flags
    ctx.rules.len().hash(&mut hasher);
    for rule in ctx.rules {
        rule.label.hash(&mut hasher);
        rule.category.hash(&mut hasher);
        rule.is_cast.hash(&mut hasher);
        rule.is_cross_category.hash(&mut hasher);
        // Hash first items as debug strings (they contain the structural info)
        for fi in &rule.first_items {
            format!("{:?}", fi).hash(&mut hasher);
        }
    }

    // Syntax patterns (label, category, items as debug strings)
    ctx.all_syntax.len().hash(&mut hasher);
    for (label, cat, items) in ctx.all_syntax {
        label.hash(&mut hasher);
        cat.hash(&mut hasher);
        for item in items {
            format!("{:?}", item).hash(&mut hasher);
        }
    }

    // BP table: hash the category operator counts
    // (BindingPowerTable doesn't implement Hash, so hash its observable behavior)
    for cat in ctx.categories {
        let ops = ctx.bp_table.operators_for_category(&cat.name);
        ops.len().hash(&mut hasher);
        for op in ops {
            op.terminal.hash(&mut hasher);
        }
    }

    // Cast/cross rules
    ctx.cast_rules.len().hash(&mut hasher);
    ctx.cross_rules.len().hash(&mut hasher);

    // RD rules
    ctx.rd_rules.len().hash(&mut hasher);

    hasher.finish()
}

/// Path to the lint cache file inside the target directory.
fn lint_cache_path() -> std::path::PathBuf {
    // Use OUT_DIR if available (proc-macro build), fall back to target/prattail
    let base = std::env::var("OUT_DIR")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|_| std::path::PathBuf::from("target/prattail"));
    base.join("lint_cache.bin")
}

/// Try to load a cached lint hash from disk.
///
/// Returns `Some(hash)` if the cache file exists and is readable.
pub fn try_load_cached_lint_hash() -> Option<u64> {
    let path = lint_cache_path();
    let data = std::fs::read(&path).ok()?;
    if data.len() == 8 {
        Some(u64::from_le_bytes(data.try_into().ok()?))
    } else {
        None
    }
}

/// Save a lint hash to the cache file.
///
/// Creates the parent directory if it does not exist.
pub fn save_lint_cache(hash: u64) {
    let path = lint_cache_path();
    if let Some(parent) = path.parent() {
        let _ = std::fs::create_dir_all(parent);
    }
    let _ = std::fs::write(&path, hash.to_le_bytes());
}

/// Run lints with DB04 caching support.
///
/// If `use_cache` is true:
/// 1. Compute a structural hash of the grammar spec
/// 2. Check if the cached hash matches
/// 3. If match: skip all lints (return empty diagnostics + an I18 note)
/// 4. If mismatch: run full lints, save the new hash, return diagnostics
///
/// If `use_cache` is false, delegates directly to [`run_lints`].
pub fn run_lints_cached(ctx: &LintContext, use_cache: bool) -> Vec<LintDiagnostic> {
    if !use_cache {
        return run_lints(ctx);
    }

    let grammar_hash = compute_grammar_hash(ctx);
    let cached_hash = try_load_cached_lint_hash();

    if cached_hash == Some(grammar_hash) {
        // Cache hit: skip all lints
        return vec![LintDiagnostic {
            id: DiagnosticId::I18,
            name: "lint-cache-hit",
            severity: LintSeverity::Info,
            category: None,
            rule: None,
            message: format!(
                "DB04 lint cache hit (hash={:#018x}): skipping {} lint passes",
                grammar_hash,
                // Approximate lint count from the run_lints function
                60,
            ),
            hint: Some("delete target/prattail/lint_cache.bin to force re-linting".to_string()),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        }];
    }

    // Cache miss: run full lints
    let diagnostics = run_lints(ctx);

    // Save the hash for next build
    save_lint_cache(grammar_hash);

    diagnostics
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
    // Stage 10c (2026-05-04): W10 + W11 deleted; see comment blocks above
    // their former emit functions. Pipeline call sites removed in lockstep.
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
    // Stage 10c (2026-05-04): P02 deleted; pipeline call site removed.
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
    lint_d13_semantic_trie_correlation(ctx, &mut diagnostics);

    // ── Mathematical analysis lints ──

    // TRS analysis (confluence + termination)
    {
        lint_t01_non_joinable_critical_pair(ctx, &mut diagnostics);
        lint_t02_confluence_verified(ctx, &mut diagnostics);
        lint_t03_non_terminating_cycle(ctx, &mut diagnostics);
        lint_t04_termination_verified(ctx, &mut diagnostics);
    }

    // VPA analysis
    {
        lint_v01_vpa_determinizable(ctx, &mut diagnostics);
        lint_v02_vpa_alphabet_mismatch(ctx, &mut diagnostics);
    }

    // WTA analysis
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
    lint_s04_ewpds_merge_site(ctx, &mut diagnostics);

    // ARA
    lint_s05_ara_invariant(ctx, &mut diagnostics);

    // Algebraic
    lint_s06_algebraic_summary(ctx, &mut diagnostics);

    // Petri nets
    {
        lint_n01_deadlock_risk(ctx, &mut diagnostics);
        lint_n02_unbounded_channel(ctx, &mut diagnostics);
    }

    // Nominal automata
    {
        lint_n03_scope_violation(ctx, &mut diagnostics);
        lint_n04_scope_narrowing(ctx, &mut diagnostics);
    }

    // Alternating automata
    lint_n05_non_bisimilar(ctx, &mut diagnostics);

    // LTL model checking
    {
        lint_l01_ltl_violated(ctx, &mut diagnostics);
        lint_l02_ltl_verified(ctx, &mut diagnostics);
    }

    // Provenance
    lint_e01_provenance_trace(ctx, &mut diagnostics);

    // CRA
    lint_e02_cra_cost_anomaly(ctx, &mut diagnostics);

    // Morphisms
    {
        lint_m01_morphism_gap(ctx, &mut diagnostics);
        lint_m02_morphism_preservation_failure(ctx, &mut diagnostics);
    }

    // KAT
    {
        lint_k01_hoare_failure(ctx, &mut diagnostics);
        lint_k02_kat_equivalence(ctx, &mut diagnostics);
    }

    // Symbolic automata
    {
        lint_sym01_unsatisfiable_guard(ctx, &mut diagnostics);
        lint_sym02_overlapping_guards(ctx, &mut diagnostics);
        lint_sym03_subsumed_guard(ctx, &mut diagnostics);
        lint_sym04_non_minimal_guards(ctx, &mut diagnostics);
    }

    // Weighted Büchi
    {
        lint_o01_weighted_buchi_non_convergent(ctx, &mut diagnostics);
        lint_o02_weighted_buchi_heavy_cycle(ctx, &mut diagnostics);
    }

    // Weighted Alternating (polynomial AWA) — uses existing alternating_result
    {
        lint_n06_weighted_parity_non_convergent(ctx, &mut diagnostics);
        lint_n07_weighted_branching_imbalance(ctx, &mut diagnostics);
    }

    // Weighted VPA — uses existing vpa_result
    {
        lint_v05_weighted_vpa_non_determinizable(ctx, &mut diagnostics);
        lint_v06_weighted_vpa_inclusion_failure(ctx, &mut diagnostics);
    }

    // Parity tree automata
    {
        lint_pt01_pata_emptiness_violation(ctx, &mut diagnostics);
        lint_pt02_pata_subsumption(ctx, &mut diagnostics);
        lint_pt03_pata_high_priority(ctx, &mut diagnostics);
        // OSLF Phase 5 `.1`: dead behavioral type RT-notes.
        lint_lp01_dead_behavioral_type(ctx, &mut diagnostics);
    }

    // Register automata
    {
        lint_ra01_unbound_data_reference(ctx, &mut diagnostics);
        lint_ra02_redundant_register(ctx, &mut diagnostics);
        lint_ra03_register_equivalence(ctx, &mut diagnostics);
    }

    // Probabilistic automata
    {
        lint_pr01_low_selectivity_rule(ctx, &mut diagnostics);
        lint_pr02_non_stochastic_state(ctx, &mut diagnostics);
        lint_pr03_high_entropy_category(ctx, &mut diagnostics);
        lint_pr04_expected_depth_anomaly(ctx, &mut diagnostics);
    }

    // Multi-tape automata
    {
        lint_mt01_multi_channel_overlap(ctx, &mut diagnostics);
        lint_mt02_multi_tape_disconnected(ctx, &mut diagnostics);
    }

    // Multiset automata
    {
        lint_ms01_unsatisfiable_cardinality(ctx, &mut diagnostics);
        lint_ms02_redundant_feature_check(ctx, &mut diagnostics);
    }

    // Weighted MSO logic
    {
        lint_mso01_unrestricted_universal_set(ctx, &mut diagnostics);
        lint_mso02_non_recognizable_step(ctx, &mut diagnostics);
        lint_mso03_equivalent_formulas(ctx, &mut diagnostics);
    }

    // Two-way transducers
    {
        lint_tw01_circular_channel_dependency(ctx, &mut diagnostics);
        lint_tw02_one_way_sufficient(ctx, &mut diagnostics);
        lint_tw03_constraint_propagation_divergent(ctx, &mut diagnostics);
    }

    // Symbolic finite transducers
    {
        lint_sft01_empty_domain(ctx, &mut diagnostics);
        lint_sft02_constant_output(ctx, &mut diagnostics);
        lint_sft03_nondeterministic(ctx, &mut diagnostics);
        lint_sft04_equivalent_pair(ctx, &mut diagnostics);
    }

    // E-graph equality saturation
    {
        lint_eg01_discovered_equivalences(ctx, &mut diagnostics);
        lint_eg02_simplifiable_guard(ctx, &mut diagnostics);
        lint_eg03_saturation_non_convergence(ctx, &mut diagnostics);
        lint_eg04_joinability_witness(ctx, &mut diagnostics);
    }

    // P06: Analysis pipeline timing
    lint_p06_analysis_pipeline_cost(ctx, &mut diagnostics);

    // ── Equation/rewrite network lints (historical A identifiers) ──
    lint_a01_fixpoint_non_convergence(ctx, &mut diagnostics);
    lint_a02_redundant_congruence(ctx, &mut diagnostics);
    lint_a03_eq_rw_category_mismatch(ctx, &mut diagnostics);
    lint_a04_large_equivalence_class(ctx, &mut diagnostics);
    lint_a05_self_referential_equation(ctx, &mut diagnostics);
    lint_a06_missing_equation_congruence(ctx, &mut diagnostics);
    lint_a07_fixpoint_iteration_anomaly(ctx, &mut diagnostics);
    lint_a08_equation_subsumes_rewrite(ctx, &mut diagnostics);
    lint_a09_generated_network_size(ctx, &mut diagnostics);
    lint_a10_unreachable_equation_variable(ctx, &mut diagnostics);

    // ── Lexer lints ──
    lint_lex01_overlapping_token_defs(ctx, &mut diagnostics);
    lint_lex02_unreachable_token_pattern(ctx, &mut diagnostics);
    lint_lex03_excessive_equiv_classes(ctx, &mut diagnostics);
    lint_lex04_dfa_state_explosion(ctx, &mut diagnostics);
    lint_lex05_float_integer_ambiguity(ctx, &mut diagnostics);

    // ── Parser lints ──
    lint_par01_deep_rd_chain(ctx, &mut diagnostics);
    lint_par02_unused_bp_level(ctx, &mut diagnostics);
    lint_par03_postfix_prefix_collision(ctx, &mut diagnostics);
    lint_par04_mixfix_ambiguous_delimiter(ctx, &mut diagnostics);
    // Stage 10.8 (2026-05-05): lint_par05_trampoline_frame_variant_count DELETED.

    // ── Dispatch lints ──
    lint_dis01_hot_path_misalignment(ctx, &mut diagnostics);
    lint_dis02_cold_arm_ratio(ctx, &mut diagnostics);
    lint_dis03_decision_tree_depth(ctx, &mut diagnostics);
    lint_dis04_backtrack_elimination_coverage(ctx, &mut diagnostics);
    lint_dis05_nfa_try_all_set_size(ctx, &mut diagnostics);

    // ── Predicate dispatch lints (PD01–PD04) ──
    {
        lint_pd01_degenerate_predicate(ctx, &mut diagnostics);
        lint_pd02_all_modules_activated(ctx, &mut diagnostics);
        lint_pd03_dispatch_savings(ctx, &mut diagnostics);
        lint_pd04_missing_feature_gate(ctx, &mut diagnostics);
    }

    // ── Constraint theory lints ──
    {
        lint_pb01_unsatisfiable_arithmetic_guard(ctx, &mut diagnostics);
        lint_pb02_tautological_arithmetic_guard(ctx, &mut diagnostics);
        lint_pb03_subsumed_arithmetic_guard(ctx, &mut diagnostics);
    }
    {
        lint_un01_unsatisfiable_unification_guard(ctx, &mut diagnostics);
        lint_un02_tautological_unification_guard(ctx, &mut diagnostics);
        lint_un03_subsumed_unification_guard(ctx, &mut diagnostics);
    }
    {
        lint_sl01_unsatisfiable_subtype_constraint(ctx, &mut diagnostics);
        lint_sl02_redundant_subtype_constraint(ctx, &mut diagnostics);
    }
    lint_lt01_search_bound_exceeded(ctx, &mut diagnostics);

    // ── Refinement type lints ──
    {
        lint_rt01_unsatisfiable_refinement(ctx, &mut diagnostics);
        lint_rt02_tautological_refinement(ctx, &mut diagnostics);
        lint_rt03_empty_intersection(ctx, &mut diagnostics);
        lint_rt04_subtype_detected(ctx, &mut diagnostics);
        lint_rt05_decidability_tier(ctx, &mut diagnostics);
        lint_rt06_name_shadow(ctx, &mut diagnostics);
        // OSLF Phase-4 `.1`: transducer dead-cast RT-notes.
        lint_rt07_dead_cast(ctx, &mut diagnostics);
        // OSLF Phase-6 `.1`: Hindley-Milner base-sort mismatch notes.
        lint_hm01_sort_mismatch(ctx, &mut diagnostics);
    }

    // ── CEK machine lints ──
    lint_cek01_dead_capture_in_frame(ctx, &mut diagnostics);
    lint_cek03_unreachable_frame_variant(ctx, &mut diagnostics);

    diagnostics
}

// ══════════════════════════════════════════════════════════════════════════════
// Per-grammar lint emission state (Lint-A cleanup)
// ══════════════════════════════════════════════════════════════════════════════
//
// The pipeline driver calls `emit_diagnostics_for_grammar` multiple times per
// grammar (once after decision-tree analyses, once after the main lint pass).
// Without coalescing, the user sees two `linting grammar` headers and two
// `summary` lines per grammar, which is confusing.
//
// The `GRAMMAR_LINT_STATE` thread-local tracks per-grammar state across calls,
// so that:
//
//   • The `linting grammar <Name>` header is printed exactly once per grammar.
//   • Severity counts accumulate across calls.
//   • A single consolidated summary is printed by `finalize_grammar_summary`
//     at the end of the pipeline (unconditionally, not only when diagnostics
//     are hidden by the severity filter).

#[derive(Debug, Default, Clone, Copy)]
pub(crate) struct GrammarLintState {
    pub(crate) header_printed: bool,
    error_count: u32,
    pub(crate) warning_count: u32,
    note_count: u32,
    info_count: u32,
    shown: u32,
}

thread_local! {
    pub(crate) static GRAMMAR_LINT_STATE: std::cell::RefCell<HashMap<String, GrammarLintState>> =
        std::cell::RefCell::new(HashMap::new());
}

/// Reset the per-grammar lint state for the current thread.
///
/// Called by tests to ensure state from one test does not leak into the
/// next. Proc-macro expansion is single-threaded per crate, so this is
/// unnecessary in production.
pub fn reset_grammar_lint_state() {
    GRAMMAR_LINT_STATE.with(|cell| cell.borrow_mut().clear());
}

/// Emit all lint diagnostics to stderr with ANSI-colorized output and a
/// grammar-name header.
///
/// **Coalescing (Lint-A cleanup).** Multiple calls for the *same grammar
/// name* are coalesced: the `linting grammar` header is printed only
/// once, and severity counts accumulate across calls. The consolidated
/// summary is printed by [`finalize_grammar_summary`] (called once per
/// grammar by the pipeline driver), not by this function.
///
/// **Verbose mode.** When `PRATTAIL_LINT_VERBOSE` is set, emits individual
/// diagnostics (useful for CI/filtering). Otherwise, groups repeated lint
/// IDs into compact summaries via [`group_diagnostics()`].
pub fn emit_diagnostics_for_grammar(grammar_name: &str, diagnostics: &[LintDiagnostic]) {
    if diagnostics.is_empty() {
        return;
    }

    // Print the header iff this is the first call for this grammar.
    let already_printed = GRAMMAR_LINT_STATE.with(|cell| {
        let mut state = cell.borrow_mut();
        let entry = state.entry(grammar_name.to_string()).or_default();
        let was_printed = entry.header_printed;
        entry.header_printed = true;
        was_printed
    });
    if !already_printed {
        eprintln!("  {}linting{} grammar `{}`", ansi::BOLD_CYAN, ansi::RESET, grammar_name,);
    }

    let verbose = std::env::var("PRATTAIL_LINT_VERBOSE").is_ok();
    let level = lint_level();
    let to_emit = if verbose {
        diagnostics.to_vec()
    } else {
        group_diagnostics(diagnostics.to_vec())
    };

    // Count by severity (on grouped set, before filtering)
    let mut error_count = 0u32;
    let mut warning_count = 0u32;
    let mut note_count = 0u32;
    let mut info_count = 0u32;
    for diag in &to_emit {
        match diag.severity {
            LintSeverity::Error => error_count += 1,
            LintSeverity::Warning => warning_count += 1,
            LintSeverity::Note => note_count += 1,
            LintSeverity::Info => info_count += 1,
        }
    }

    // Emit filtered diagnostics
    let mut shown = 0u32;
    for diag in &to_emit {
        if diag.severity >= level {
            eprintln!("{}", format_diagnostic_colored(diag));
            shown += 1;
        }
    }

    // Accumulate into per-grammar state for the consolidated summary.
    GRAMMAR_LINT_STATE.with(|cell| {
        let mut state = cell.borrow_mut();
        let entry = state.entry(grammar_name.to_string()).or_default();
        entry.error_count += error_count;
        entry.warning_count += warning_count;
        entry.note_count += note_count;
        entry.info_count += info_count;
        entry.shown += shown;
    });
}

/// Emit a single consolidated summary line for the given grammar, covering
/// all `emit_diagnostics_for_grammar` calls made for it during this
/// expansion.
///
/// Should be called *once* per grammar by the pipeline driver, after all
/// lint passes have finished. If no diagnostics were ever emitted for
/// this grammar, this function is a no-op.
///
/// The summary is **unconditional**: it is printed whether or not any
/// diagnostics were hidden by `PRATTAIL_LINT_LEVEL`. This gives the
/// user a stable per-grammar overview at the tail of each grammar's
/// lint output (Lint-C cleanup).
pub fn finalize_grammar_summary(grammar_name: &str) {
    let state_opt = GRAMMAR_LINT_STATE.with(|cell| cell.borrow().get(grammar_name).copied());
    let Some(state) = state_opt else {
        return;
    };
    if !state.header_printed {
        return;
    }
    let total = state.error_count + state.warning_count + state.note_count + state.info_count;
    let hidden = total.saturating_sub(state.shown);
    if hidden > 0 {
        eprintln!(
            "  {}summary{} ({}): {} error(s), {} warning(s), {} note(s), {} info(s) [{} shown, {} hidden by PRATTAIL_LINT_LEVEL]",
            ansi::BOLD_CYAN, ansi::RESET, grammar_name,
            state.error_count, state.warning_count, state.note_count, state.info_count,
            state.shown, hidden,
        );
    } else {
        eprintln!(
            "  {}summary{} ({}): {} error(s), {} warning(s), {} note(s), {} info(s)",
            ansi::BOLD_CYAN,
            ansi::RESET,
            grammar_name,
            state.error_count,
            state.warning_count,
            state.note_count,
            state.info_count,
        );
    }
}

/// Returns true if any diagnostic has Error severity.
pub fn has_errors(diagnostics: &[LintDiagnostic]) -> bool {
    diagnostics
        .iter()
        .any(|d| d.severity == LintSeverity::Error)
}
