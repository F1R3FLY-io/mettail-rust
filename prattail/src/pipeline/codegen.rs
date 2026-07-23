use super::*;

/// Generate parser code with lexer context (variant map + ambiguity info).
///
/// Passes lexer context to `generate_parser_code()` so the composed dispatch
/// table can be computed once and used both for:
/// 1. Standard batch path: deterministic dispatch arms (no backtracking)
/// 2. Context-sensitive lex (feature-gated): Lexer struct, LexerAdapter, lazy parsers
pub(crate) fn generate_parser_code_with_context(
    bundle: &ParserBundle,
    variant_map: &TokenVariantMap,
    ambiguity_info: &LexerAmbiguityInfo,
) -> String {
    generate_parser_code(bundle, variant_map, ambiguity_info).0
}

/// Generate parser code with lexer context AND capture pipeline analysis data.
///
/// Returns both the generated code string and a [`PipelineAnalysis`] populated
/// from the pipeline's internal WFST data (dead rules, constructor weights, etc.).
pub(crate) fn generate_parser_code_with_analysis(
    bundle: &ParserBundle,
    variant_map: &TokenVariantMap,
    ambiguity_info: &LexerAmbiguityInfo,
) -> (String, crate::PipelineAnalysis) {
    generate_parser_code(bundle, variant_map, ambiguity_info)
}

/// Generate parser code from the parser bundle.
///
/// Runs: FIRST/FOLLOW sets → RD handlers → Pratt parsers → cross-category dispatch.
///
/// When `variant_map` and `ambiguity_info` are provided, computes the composed
/// dispatch table once and uses it to emit deterministic match arms in standard
/// batch dispatch (no backtracking).
///
/// Returns `(code_string, PipelineAnalysis)` where the analysis captures
/// WFST-derived data (dead rules, constructor weights, category weights)
/// for downstream optimization by the Ascent codegen in the macros crate.
fn generate_parser_code(
    bundle: &ParserBundle,
    variant_map: &TokenVariantMap,
    ambiguity_info: &LexerAmbiguityInfo,
) -> (String, crate::PipelineAnalysis) {
    let category_names: Vec<String> = bundle.categories.iter().map(|c| c.name.clone()).collect();
    let primary_category = category_names.first().map(|s| s.as_str()).unwrap_or("");

    // D07: Check if runtime coverage instrumentation is requested
    let emit_coverage = std::env::var("PRATTAIL_COVERAGE").is_ok();

    // Layer 10 incremental codegen cache scaffolding DELETED 2026-05-12:
    // the prev_cache load was never consumed (no per-category content-hash
    // check elided any codegen work) and new_cache was saved empty every
    // run. The IncrementalState type at `decision_tree.rs:2505` and the
    // `PRATTAIL_CACHE_DIR` env-var convention are preserved for a future
    // proper implementation; the half-baked I/O is removed here so the
    // cache file isn't silently produced+consumed as a no-op artifact.
    // See `prattail/docs/design/decision-tree/code-emission.md` §6.2.

    // ── DB01: Early gate check for incremental FIRST/FOLLOW ──────────────
    // The full optimization gates are computed later (after FIRST/FOLLOW and
    // WFST construction). DB01 controls HOW FIRST/FOLLOW sets are computed,
    // so we pre-check the gate here. When the env var is unset, default to
    // enabled for grammars with >=3 categories (matches cost-benefit threshold).
    let use_incremental_ff = {
        match std::env::var("PRATTAIL_AUTO_OPTIMIZE") {
            Ok(val) => {
                let trimmed = val.trim();
                if trimmed.eq_ignore_ascii_case("all") {
                    true
                } else if trimmed.eq_ignore_ascii_case("none") {
                    false
                } else {
                    // Comma-separated list: check if DB01 or IncrementalFirstFollow is present
                    trimmed.split(',').any(|part| {
                        let p = part.trim();
                        p.eq_ignore_ascii_case("DB01")
                            || p.eq_ignore_ascii_case("IncrementalFirstFollow")
                            || p.eq_ignore_ascii_case("DB01:IncrementalFirstFollow")
                    })
                }
            },
            Err(_) => category_names.len() >= 3, // Default: enable for non-trivial grammars
        }
    };

    // Compute FIRST sets (DB01: incremental when gate is active)
    let (mut first_sets, first_stats) = if use_incremental_ff {
        compute_first_sets_incremental(&bundle.rule_infos, &category_names)
    } else {
        (compute_first_sets(&bundle.rule_infos, &category_names), Default::default())
    };

    // Augment FIRST sets with native literal tokens
    for cat in &bundle.categories {
        if let Some(ref native_type) = cat.native_type {
            if let Some(first_set) = first_sets.get_mut(&cat.name) {
                match native_type.as_str() {
                    "i32" | "i64" | "u32" | "u64" | "isize" | "usize" => {
                        first_set.insert("Integer");
                    },
                    "f32" | "f64" => {
                        first_set.insert("Float");
                    },
                    "bool" => {
                        first_set.insert("Boolean");
                    },
                    "str" | "String" => {
                        first_set.insert("StringLit");
                    },
                    // BigRat/Fixed/BigInt literal Tokens are category-named
                    // (e.g. `Token::BigRat`, `Token::Fixed`, `Token::BigInt`) —
                    // the lexer emits them ONLY when the source matches the
                    // category-specific regex (`…r`, `…p…`, `…n`). FIRST
                    // sets reflect the category-named variant so the parser
                    // dispatches on the correct variant; a bare integer like
                    // `1` does NOT dispatch to BigInt — it dispatches to
                    // Int (built-in `Token::Integer`).
                    _ if native_type.ends_with("CanonicalBigRat") => {
                        first_set.insert(&cat.name);
                    },
                    _ if native_type.ends_with("CanonicalFixedPoint") => {
                        first_set.insert(&cat.name);
                    },
                    _ if native_type.ends_with("CanonicalBigInt") => {
                        first_set.insert(&cat.name);
                    },
                    _ => {},
                }
            }
        }
    }

    // Augment FIRST sets with custom tokens targeting each category.
    // Custom tokens with `: Category` (e.g., `HexLiteral : Int`) produce
    // additional literal values for that category, so the category's FIRST
    // set must include the custom token's variant name.
    for spec in &bundle.custom_tokens {
        if let Some(ref cat_name) = spec.category {
            if let Some(first_set) = first_sets.get_mut(cat_name.as_str()) {
                first_set.insert(&spec.name);
            }
        }
    }

    // Augment FIRST sets with Ident for all categories.
    // Every category has auto-generated Var rules (e.g., IVar, BVar, FVar, SVar)
    // that accept Token::Ident as a prefix. These rules are synthesized by the
    // macros crate during code generation (not in LanguageSpec.rules), so the
    // fixed-point FIRST set computation doesn't see them. Without this, cross-
    // category dispatch never generates arms for Ident tokens, causing expressions
    // like `x >= 1` to fall through to the own-category parser and fail.
    for cat_name in &category_names {
        if let Some(first_set) = first_sets.get_mut(cat_name) {
            first_set.insert("Ident");
        }
    }

    // Augment FIRST sets with LParen for all categories.
    // Every category supports parenthesized grouping: `( expr )`.
    // Without this, cross-category dispatch classifies LParen as "unique to
    // source" (deterministic) instead of "ambiguous between source and target".
    // This causes deterministic arms to commit to a cross-category parse path
    // without fallback, breaking expressions like `(3+2)! == 120` where the
    // grouped arithmetic should be tried via both paths. Including LParen in
    // all FIRST sets makes it an ambiguous dispatch token, triggering save/
    // restore with proper fallback to parse_Cat_own.
    for cat_name in &category_names {
        if let Some(first_set) = first_sets.get_mut(cat_name) {
            first_set.insert("LParen");
        }
    }

    // Augment FIRST set of primary category with Caret and dollar tokens if grammar has binders
    if bundle.has_binders {
        if let Some(first_set) = first_sets.get_mut(primary_category) {
            first_set.insert("Caret");
            // Add dollar tokens: DollarProc, DdollarProcLp, etc.
            for cat in &bundle.categories {
                let cat_lower = cat.name.to_lowercase();
                let capitalized = capitalize_first(&cat_lower);
                first_set.insert(&format!("Dollar{}", capitalized));
                first_set.insert(&format!("Ddollar{}Lp", capitalized));
            }
        }
    }

    let overlaps = analyze_cross_category_overlaps(&category_names, &first_sets);

    // Compute FOLLOW sets (DB01: incremental when gate is active)
    let (follow_sets, follow_stats) = if use_incremental_ff {
        compute_follow_sets_incremental(
            &bundle.follow_inputs,
            &category_names,
            &first_sets,
            primary_category,
        )
    } else {
        (
            compute_follow_sets_from_inputs(
                &bundle.follow_inputs,
                &category_names,
                &first_sets,
                primary_category,
            ),
            Default::default(),
        )
    };

    // ── DB01: Emit I18 diagnostic if incremental mode reduced work ────────
    if use_incremental_ff && (first_stats.reduced_work() || follow_stats.reduced_work()) {
        let first_baseline = first_stats.total_categories * first_stats.iterations;
        let follow_baseline = follow_stats.total_categories * follow_stats.iterations;
        pipeline_diagnostic(
            &bundle.grammar_name,
            DiagnosticId::I18,
            "incremental-first-follow",
            crate::lint::LintSeverity::Info,
            format!(
                "DB01 incremental FIRST/FOLLOW: FIRST {}/{} visits ({} iters, {} cats), \
                 FOLLOW {}/{} visits ({} iters, {} cats)",
                first_stats.total_visits,
                first_baseline,
                first_stats.iterations,
                first_stats.total_categories,
                follow_stats.total_visits,
                follow_baseline,
                follow_stats.iterations,
                follow_stats.total_categories,
            ),
            Some(format!(
                "FIRST max/iter={}, FOLLOW max/iter={} (vs {} total categories)",
                first_stats.max_visits_per_iteration,
                follow_stats.max_visits_per_iteration,
                category_names.len(),
            )),
        );
    }

    // ── WFST construction ─────────────────────────────────────────────────
    // Build prediction WFSTs and recovery WFSTs from FIRST/FOLLOW/overlap data.
    // These are consulted by weighted dispatch and recovery codegen below.
    let (mut prediction_wfsts, mut recovery_wfsts, token_id_map) = {
        use crate::prediction::build_dispatch_action_tables;
        use crate::recovery::build_recovery_wfsts;
        use crate::token_id::TokenIdMap;
        use crate::wfst::build_prediction_wfsts;

        // Build native type map for dispatch action table extraction
        let native_types: std::collections::HashMap<String, Option<String>> = bundle
            .categories
            .iter()
            .map(|c| (c.name.clone(), c.native_type.clone()))
            .collect();

        // Build dispatch action tables (structured data for WFST weight assignment)
        let dispatch_actions = build_dispatch_action_tables(
            &category_names,
            &first_sets,
            &overlaps,
            &bundle.rd_rules,
            &bundle.cross_rules,
            &bundle.cast_rules,
            &native_types,
        );

        // Build prediction WFSTs (per-category, weight-ordered dispatch)
        let mut prediction_wfsts =
            build_prediction_wfsts(&category_names, &first_sets, &overlaps, &dispatch_actions);

        // Enrich WFSTs with two-token disambiguation paths.
        // For NFA-ambiguous groups where the second position (terminal or FIRST-expanded
        // nonterminal) uniquely identifies the rule, adds start → intermediate → accept
        // paths so predict_two_token() can resolve them.
        let two_token_paths_added = crate::wfst::enrich_with_two_token_paths(
            &mut prediction_wfsts,
            &bundle.rd_rules,
            &category_names,
            &first_sets,
        );
        if two_token_paths_added > 0 {
            pipeline_diagnostic(
                &bundle.grammar_name,
                DiagnosticId::I02,
                "two-token-enrichment",
                crate::lint::LintSeverity::Info,
                format!(
                    "{} two-token disambiguation path(s) added to prediction WFSTs",
                    two_token_paths_added
                ),
                None,
            );
        }

        // Sprint 3: Assign ContextWeight bit positions to rules in each WFST.
        // For each category's PredictionWfst, find dispatch tokens that have
        // multiple competing rules (ambiguous groups). Assign sequential bit IDs
        // (0..N-1) to the rule labels so that `live_rules_context_after()` can
        // track which rules survive after consuming tokens.
        {
            let mut total_context_labels = 0usize;
            for wfst in prediction_wfsts.values_mut() {
                // Collect unique rule labels from all actions
                let mut rule_labels: Vec<String> =
                    wfst.actions.iter().map(|a| a.action.rule_label()).collect();
                rule_labels.sort();
                rule_labels.dedup();
                if rule_labels.len() > 1 {
                    let label_refs: Vec<&str> = rule_labels.iter().map(|s| s.as_str()).collect();
                    wfst.assign_context_labels(&label_refs);
                    total_context_labels += rule_labels.len();
                }
            }
            if total_context_labels > 0 {
                pipeline_diagnostic(
                    &bundle.grammar_name,
                    DiagnosticId::I03,
                    "context-weight-labels",
                    crate::lint::LintSeverity::Info,
                    format!(
                        "{} ContextWeight bit labels assigned across prediction WFSTs",
                        total_context_labels
                    ),
                    None,
                );
            }
        }

        // B3: WFST minimization gate — skip cascade for trivial grammars.
        // The threshold is 4 WFST states: grammars below this (e.g., Lambda with
        // 2 states) gain no benefit from the cascade. Computed early (before the
        // cascade) using only total_wfst_states, which is available immediately
        // after build_prediction_wfsts().
        let total_wfst_states: usize = prediction_wfsts.values().map(|w| w.states.len()).sum();
        let run_cascade = total_wfst_states > 4;

        // E1: Transducer cascade — compose optimization passes into a fixed-point pipeline.
        // Replaces the standalone B3 minimization and beam width blocks with a unified
        // cascade that runs weight normalization → dead-state elimination → minimization
        // (→ beam pruning if configured) until convergence.
        // B3: Gated by WFST state count — trivial grammars skip the cascade.
        if run_cascade {
            let cascade = if let Some(beam_value) = bundle.beam_width.to_option() {
                crate::transducer::TransducerCascade::with_beam(beam_value)
            } else {
                crate::transducer::TransducerCascade::default_pipeline()
            };
            let summary = cascade.run_all(&mut prediction_wfsts);
            if !summary.is_empty() {
                pipeline_diagnostic(
                    &bundle.grammar_name,
                    DiagnosticId::I01,
                    "transducer-cascade",
                    crate::lint::LintSeverity::Info,
                    summary,
                    None,
                );
            }
        } else {
            pipeline_diagnostic(
                &bundle.grammar_name,
                DiagnosticId::I02,
                "cascade-skipped",
                crate::lint::LintSeverity::Info,
                format!("skipping transducer cascade ({} WFST states ≤ 4)", total_wfst_states),
                None,
            );
        }

        // Apply beam width configuration (stored on WFST for runtime predict_pruned)
        match &bundle.beam_width {
            crate::BeamWidthConfig::Explicit(beam_value) => {
                let beam = crate::automata::semiring::TropicalWeight::new(*beam_value);
                for wfst in prediction_wfsts.values_mut() {
                    wfst.set_beam_width(Some(beam));
                }
            },
            crate::BeamWidthConfig::Auto => {
                // A7: Entropy-based adaptive beam width per category.
                // When wfst-log is enabled, compute per-category Shannon entropy and
                // derive beam widths. Higher-entropy categories get wider beams.
                {
                    for (cat_name, wfst) in prediction_wfsts.iter_mut() {
                        let (_entropy_nats, entropy_bits) = wfst.compute_entropy();
                        let beam_opt = crate::wfst::entropy_to_beam_width(
                            entropy_bits,
                            crate::wfst::ENTROPY_BEAM_BASE,
                            crate::wfst::ENTROPY_BEAM_SCALE,
                            crate::wfst::ENTROPY_BEAM_LOW_THRESHOLD,
                            crate::wfst::ENTROPY_BEAM_MAX,
                        );
                        if let Some(beam_value) = beam_opt {
                            let beam = crate::automata::semiring::TropicalWeight::new(beam_value);
                            wfst.set_beam_width(Some(beam));
                            pipeline_diagnostic(
                                &bundle.grammar_name,
                                DiagnosticId::I03,
                                "adaptive-beam",
                                crate::lint::LintSeverity::Info,
                                format!(
                                    "{}: entropy={:.2} bits → beam={:.2}",
                                    cat_name, entropy_bits, beam_value
                                ),
                                None,
                            );
                        } else {
                            pipeline_diagnostic(
                                &bundle.grammar_name,
                                DiagnosticId::I03,
                                "adaptive-beam",
                                crate::lint::LintSeverity::Info,
                                format!(
                                    "{}: entropy={:.2} bits → no beam (deterministic)",
                                    cat_name, entropy_bits
                                ),
                                None,
                            );
                        }
                    }
                }
                // Without wfst-log, Auto falls back to Disabled (no beam).
            },
            crate::BeamWidthConfig::Disabled => {},
        }

        // NOTE: Dead-rule detection (W01) now handled by lint::run_lints() below.

        // Build token ID map from all FIRST set tokens (shared across recovery WFSTs)
        let mut all_tokens: Vec<String> = Vec::new();
        for first_set in first_sets.values() {
            all_tokens.extend(first_set.tokens.iter().cloned());
        }
        // Also include FOLLOW set tokens and structural tokens for recovery
        for follow_set in follow_sets.values() {
            all_tokens.extend(follow_set.tokens.iter().cloned());
        }
        all_tokens.push("Eof".to_string());
        all_tokens.push("RParen".to_string());
        all_tokens.push("RBrace".to_string());
        all_tokens.push("RBracket".to_string());
        all_tokens.push("Semi".to_string());
        all_tokens.push("Comma".to_string());
        let token_id_map = TokenIdMap::from_names(all_tokens);

        // Collect grammar terminals for recovery WFST construction
        let grammar_terminals_wfst: std::collections::HashSet<String> = {
            let mut terminals = std::collections::HashSet::new();
            for input in &bundle.follow_inputs {
                for t in collect_terminals_recursive(&input.syntax) {
                    terminals.insert(t);
                }
            }
            for delim in &["(", ")", "{", "}", "[", "]", ","] {
                terminals.insert(delim.to_string());
            }
            if bundle.has_binders {
                terminals.insert("^".to_string());
                terminals.insert(".".to_string());
            }
            terminals
        };

        // Build recovery WFSTs (per-category, weighted repair strategies)
        // B1: Thread prediction WFSTs into recovery construction for prediction-aware
        // discount factors on sync tokens (Tier 4 cost adjustment).
        let recovery_wfsts = build_recovery_wfsts(
            &category_names,
            &follow_sets,
            &grammar_terminals_wfst,
            &token_id_map,
            Some(&prediction_wfsts),
        );

        (prediction_wfsts, recovery_wfsts, token_id_map)
    };

    // ── WFST static embedding ─────────────────────────────────────────────
    // Emit prediction WFSTs as CSR-format static arrays with LazyLock constructors.
    // This makes the WFST data available at runtime for dynamic prediction
    // (e.g., with trained model weights overriding heuristic weights).
    let mut buf = String::with_capacity(8192);
    emit_prediction_wfst_static(&mut buf, &prediction_wfsts);
    // Stage 10.5r-d (2026-05-05): emit_recovery_wfst_static + emit_parse_simulator_static
    // calls DELETED. Both emit data structures consumed only by the dead
    // `wfst_recover_<Cat>` function (also deleted). RECOVERY_BEAM_WIDTH constant
    // similarly dead — removed.

    // Compute the set of token variant names that actually exist in the grammar's
    // Token enum. The TokenIdMap may contain superset tokens (e.g., Semi) that don't
    // appear in all grammars — emitting match arms for non-existent variants causes errors.
    let grammar_token_variants: std::collections::HashSet<String> = {
        let mut variants = std::collections::HashSet::new();
        // Always present
        variants.insert("Eof".to_string());
        variants.insert("Ident".to_string());
        // Native-type-derived builtin tokens
        for cat in &bundle.categories {
            match cat.native_type.as_deref() {
                Some("i32" | "i64" | "u32" | "u64" | "usize" | "isize") => {
                    variants.insert("Integer".to_string());
                },
                Some("f32" | "f64") => {
                    variants.insert("Float".to_string());
                },
                Some("bool") => {
                    variants.insert("Boolean".to_string());
                },
                Some("String" | "&str") => {
                    variants.insert("StringLit".to_string());
                },
                _ => {},
            }
        }
        // Structural delimiters (always in Token enum)
        for v in &["LParen", "RParen", "LBrace", "RBrace", "LBracket", "RBracket", "Comma"] {
            variants.insert(v.to_string());
        }
        // All FIRST set tokens (these must be in the Token enum)
        for fs in first_sets.values() {
            for tok in fs.sorted_tokens() {
                variants.insert(tok.to_string());
            }
        }
        // All FOLLOW set tokens
        for fs in follow_sets.values() {
            for tok in fs.sorted_tokens() {
                variants.insert(tok.to_string());
            }
        }
        variants
    };

    // Emit token_to_id helper for Tier 3 simulation (Token → u16 TokenId).
    // Build a set of token names that carry a payload (tuple-variant patterns
    // must use a wildcard, e.g. `Token::BigRat(_)` not `Token::BigRat`).
    let payload_variants: std::collections::HashSet<String> = {
        let mut set = std::collections::HashSet::new();
        for spec in &bundle.custom_tokens {
            if spec.payload_type.is_some() {
                set.insert(spec.name.clone());
            }
        }
        set
    };

    emit_token_to_id_fn(&mut buf, &token_id_map, &grammar_token_variants, &payload_variants);

    // Stage 10.5 (2026-05-04): RD handler emission (`all_prefix_handlers` Vec
    // build + lambda/dollar handler block) DELETED. These emitters fed the
    // now-deleted trampoline emission. Walker emits binder syntax via
    // `wpda_codegen/binder.rs` (lambda/dollar) and prefix RD rules via
    // `wpda_codegen/prefix.rs`.
    //
    // Stage 10.5 (2026-05-04): `dispatch_categories` declaration DELETED.
    // It fed `TrampolineConfig::needs_dispatch` and the cross-cat dispatch
    // for-loop, both of which died with the trampoline.

    // ── Composed dispatch resolution ────────────────────────────────────────
    // Compute the composed dispatch table from lexer ambiguity info and
    // FIRST sets. This is used at codegen time to resolve ambiguous tokens
    // deterministically — eliminating save/restore backtracking in the
    // standard batch path. Computed before trampoline generation so that
    // composed weights are available for ident-lookahead handler sorting.
    use crate::prediction::{
        build_complete_weight_map, compute_composed_dispatch, resolve_dispatch_winners,
    };

    let (composed_resolutions, complete_weight_map, w05_diagnostics) = if ambiguity_info
        .has_ambiguous
    {
        let (composed, w05_diags) = compute_composed_dispatch(
            &ambiguity_info.ambiguous_states,
            &category_names,
            &first_sets,
            variant_map,
            Some(&prediction_wfsts),
            &bundle.rule_infos,
            &bundle.grammar_name,
        );

        // Build complete weight map covering ALL (category, token) pairs.
        // Ambiguous tokens use composed dispatch weights; deterministic tokens
        // use rule specificity weights. Used for dispatch arm ordering.
        let weight_map =
            build_complete_weight_map(&composed, &first_sets, &bundle.rule_infos, &category_names);

        (Some(resolve_dispatch_winners(&composed)), Some(weight_map), w05_diags)
    } else {
        // No ambiguous states — still build weight map for deterministic tokens
        let weight_map = build_complete_weight_map(
            &HashMap::new(),
            &first_sets,
            &bundle.rule_infos,
            &category_names,
        );
        (None, Some(weight_map), Vec::new())
    };

    // Detect which categories have NFA-ambiguous prefix groups (multiple rules
    // sharing the same dispatch token). These categories need thread-local spillover
    // buffers and forced-prefix replay for intra-category disambiguation.
    let mut nfa_spillover_categories =
        crate::rd_analysis::categories_needing_nfa_spillover(&bundle.rd_rules, &category_names);

    // ── D1 + A3: Cost-benefit optimization analysis → optimization gating ──
    // Profile the grammar and evaluate which optimizations are beneficial.
    // Results are used to populate OptimizationGates, which controls which
    // compile-time optimization passes are emitted in codegen. This makes
    // the pipeline self-tuning per grammar.
    // The grammar_profile is computed once and reused for the D2 complexity report.
    let empty_dt: HashMap<String, crate::decision_tree::CategoryDecisionTree> = HashMap::new();
    let mut grammar_profile = crate::cost_benefit::build_grammar_profile(
        &prediction_wfsts,
        &first_sets,
        &nfa_spillover_categories,
        bundle.rule_infos.len(),
        bundle.beam_width.is_enabled(),
        &empty_dt,
    );
    let optimization_gates = {
        let recommended = crate::cost_benefit::recommended_optimizations(&grammar_profile);
        let gates =
            crate::cost_benefit::OptimizationGates::from_env_or_recommendations(&recommended);
        if !recommended.is_empty() {
            let verbose = std::env::var("PRATTAIL_LINT_VERBOSE").is_ok();
            let detail_lines: Vec<String> = recommended
                .iter()
                .map(|c| {
                    format!(
                        "  {} (speedup={:.2}, cost={:.2}): {}",
                        c.optimization,
                        c.speedup.value(),
                        c.compile_cost.value(),
                        c.reason
                    )
                })
                .collect();
            let display_lines = if !verbose && detail_lines.len() > 5 {
                let mut truncated = detail_lines[..5].to_vec();
                truncated.push(format!(
                    "  ... and {} more (set PRATTAIL_LINT_VERBOSE=1 to see all)",
                    detail_lines.len() - 5
                ));
                truncated
            } else {
                detail_lines
            };
            pipeline_diagnostic(
                &bundle.grammar_name,
                DiagnosticId::I05,
                "cost-benefit-recommendations",
                crate::lint::LintSeverity::Info,
                format!(
                    "cost-benefit analysis recommends {} optimization(s):\n{}",
                    recommended.len(),
                    display_lines.join("\n"),
                ),
                None,
            );
        }
        gates
    };

    // ── A4: Dead-rule collection ─────────────────────────────────────────
    // Always compute dead rule labels for PipelineAnalysis export (consumed
    // by Ascent DCE in Sprint 1). When the enhanced_dce gate is also enabled,
    // these labels are additionally threaded into dispatch and trampoline
    // configs to suppress parser codegen for unreachable rules.
    // The lint layer still emits W01 warnings independently.
    let mut all_dead_rule_labels = collect_dead_rule_labels_with_ignored(
        &bundle.rule_infos,
        &bundle.categories,
        &first_sets,
        &prediction_wfsts,
        &bundle.semantic_dependency_groups,
        &HashMap::new(), // DTs are built after this pass; trie confirmation happens in pass 2 below
        &bundle.rd_rules,
        &bundle.dead_rule_ignore_labels,
    );
    let dead_rules: HashSet<String> = if optimization_gates.enhanced_dce {
        if !all_dead_rule_labels.is_empty() {
            let mut sorted: Vec<&str> = all_dead_rule_labels.iter().map(|s| s.as_str()).collect();
            sorted.sort_unstable();
            pipeline_diagnostic(
                &bundle.grammar_name,
                DiagnosticId::I06,
                "enhanced-dce-active",
                crate::lint::LintSeverity::Info,
                format!(
                    "enhanced DCE: suppressing codegen for {} dead rule(s): [{}]",
                    all_dead_rule_labels.len(),
                    sorted.join(", "),
                ),
                None,
            );
        }
        all_dead_rule_labels.clone()
    } else {
        HashSet::new()
    };

    // ── Decision tree construction ─────────────────────────────────────────
    // Build PathMap decision trees for all categories. The tree subsumes the
    // ad-hoc dispatch analyses (group_rd_by_dispatch_token, shared prefix,
    // second-token lookahead, suffix disjointness, etc.) into a single
    // unified trie-based mechanism. Built after FIRST sets and dead rules
    // are available; threaded into TrampolineConfig for codegen queries.
    // ── D-B02: Lazy analysis skip — decision tree ──────────────────────────
    // Skip decision tree construction for trivial grammars with fewer than 3
    // total rules (rd + cross + cast), where trie dispatch provides no benefit.
    let total_rule_count =
        bundle.rd_rules.len() + bundle.cross_rules.len() + bundle.cast_rules.len();

    let decision_trees = {
        use crate::decision_tree::DecisionTreeBuilder;
        let mut dt_builder = DecisionTreeBuilder::new(
            token_id_map.clone(),
            first_sets.clone(),
            category_names.clone(),
            dead_rules.clone(),
        );

        if total_rule_count >= 3 {
            dt_builder.build_all(&bundle.rd_rules, &bundle.cross_rules, &bundle.cast_rules);

            // ── Decision-tree diagnostics (D01–D09) ─────────────────────────────
            // Collect all DT diagnostics into a single Vec, then emit via the
            // standard lint framework for batching, grouping, and PRATTAIL_LINT_VERBOSE.
            let mut dt_diagnostics: Vec<crate::lint::LintDiagnostic> = Vec::new();

            for cat_name in &category_names {
                if let Some(tree) = dt_builder.get_tree(cat_name) {
                    // D05: complexity metrics
                    if tree.stats.total_states > 0 {
                        dt_diagnostics.push(crate::decision_tree::complexity_metrics(
                            tree,
                            &bundle.grammar_name,
                        ));
                    }

                    // D01: precision ambiguity
                    dt_diagnostics.extend(crate::decision_tree::precision_ambiguity_reports(
                        tree,
                        &token_id_map,
                        &bundle.grammar_name,
                    ));

                    // D02: unresolvable ambiguity
                    dt_diagnostics.extend(crate::decision_tree::unresolvable_ambiguity_reports(
                        tree,
                        &token_id_map,
                        &bundle.grammar_name,
                    ));

                    // D03: unreachable rules
                    let all_labels: std::collections::HashSet<String> = bundle
                        .rd_rules
                        .iter()
                        .filter(|r| {
                            r.category == *cat_name && !r.is_collection && r.prefix_bp.is_none()
                        })
                        .filter(|r| {
                            !matches!(
                                r.items.first(),
                                Some(crate::grammar::ir::RDSyntaxItem::NonTerminal { .. })
                                    | Some(crate::grammar::ir::RDSyntaxItem::IdentCapture { .. })
                            )
                        })
                        .map(|r| r.label.clone())
                        .collect();
                    dt_diagnostics.extend(crate::decision_tree::unreachable_rule_detection(
                        tree,
                        &all_labels,
                        &bundle.grammar_name,
                    ));

                    // D04: min lookahead
                    if tree.stats.total_states > 0 {
                        dt_diagnostics.push(crate::decision_tree::min_lookahead_report(
                            tree,
                            &bundle.grammar_name,
                        ));
                    }
                }

                // D06: WFST consistency (needs both tree and wfst)
                if let (Some(tree), Some(wfst)) =
                    (dt_builder.get_tree(cat_name), prediction_wfsts.get(cat_name))
                {
                    dt_diagnostics.extend(crate::decision_tree::wfst_consistency_check(
                        tree,
                        wfst,
                        &token_id_map,
                        &bundle.grammar_name,
                    ));
                }

                if let Some(tree) = dt_builder.get_tree(cat_name) {
                    // D08: optimization suggestions
                    dt_diagnostics.extend(crate::decision_tree::optimization_suggestions(
                        tree,
                        &bundle.grammar_name,
                    ));

                    // D09: conflict resolution guidance
                    dt_diagnostics.extend(crate::decision_tree::conflict_resolution_guidance(
                        tree,
                        &bundle.grammar_name,
                    ));
                }
            }

            crate::lint::emit_diagnostics_for_grammar(&bundle.grammar_name, &dt_diagnostics);
        } else {
            pipeline_diagnostic(
                &bundle.grammar_name,
                DiagnosticId::I15,
                "lazy-analysis-skip",
                crate::lint::LintSeverity::Info,
                format!(
                    "decision tree construction skipped: {} rule(s) < 3 threshold",
                    total_rule_count,
                ),
                None,
            );
        }

        dt_builder
    };

    // ── Update grammar_profile with PathMap decision tree metrics ──────────
    {
        let dt_trees = decision_trees.trees();
        if !dt_trees.is_empty() {
            let mut total_depth = 0usize;
            let mut total_ambiguous = 0usize;
            let mut total_states = 0usize;
            let mut total_det_rules = 0usize;
            let mut total_rules = 0usize;
            for tree in dt_trees.values() {
                total_depth += tree.stats.max_depth;
                total_ambiguous += tree.stats.ambiguous_nodes;
                total_states += tree.stats.total_states;
                total_det_rules += tree.stats.deterministic_rules;
                total_rules += tree.stats.total_rules;
            }
            let n = dt_trees.len() as f64;
            grammar_profile.avg_trie_depth = total_depth as f64 / n;
            grammar_profile.ambiguity_score = if total_states > 0 {
                total_ambiguous as f64 / total_states as f64
            } else {
                0.0
            };
            grammar_profile.deterministic_ratio = if total_rules > 0 {
                total_det_rules as f64 / total_rules as f64
            } else {
                1.0
            };
        }
    }

    // ── 2a: Dispatch entropy analysis (optional) ───────────────────────────
    // Gated by the `walker-trace` feature + PRATTAIL_ENTROPY=1. Reports
    // per-category dispatch entropy to identify "decision bottlenecks" — tokens
    // where grammar restructuring would have maximum disambiguation impact. The
    // env read is compiled out on the default build.
    trace_diag! {
    if std::env::var("PRATTAIL_ENTROPY").is_ok() {
        let dt_trees = decision_trees.trees();
        for (cat_name, tree) in dt_trees {
            let profile = tree.entropy_profile();
            if !profile.is_empty() {
                let lines: Vec<String> = profile.iter()
                    .take(5) // top 5 bottlenecks
                    .filter_map(|(byte, entropy, count)| {
                        token_id_map.name(*byte as u16).map(|name|
                            format!("{}: H={:.3}, {} rule(s)", name, entropy, count)
                        )
                    })
                    .collect();
                if !lines.is_empty() {
                    pipeline_diagnostic(
                        &bundle.grammar_name,
                        DiagnosticId::D11,
                        "dispatch-entropy",
                        crate::lint::LintSeverity::Note,
                        format!(
                            "category {}: dispatch entropy (top bottlenecks): {}",
                            cat_name,
                            lines.join("; "),
                        ),
                        None,
                    );
                }
            }
        }
    }
    }

    // ── 2b: BP/dispatch correlation analysis (optional) ────────────────────
    // Gated by the `walker-trace` feature + PRATTAIL_ENTROPY=1 (shared with the
    // entropy analysis). Reports per-category BP stratification: how many rules
    // are reachable at each binding power level, enabling early-commit
    // optimizations. The env read is compiled out on the default build.
    trace_diag! {
    if std::env::var("PRATTAIL_ENTROPY").is_ok() {
        let dt_trees = decision_trees.trees();
        for (cat_name, tree) in dt_trees {
            // Build a rule→BP map from the bp_table for this category
            let bp_map: HashMap<String, u8> = bundle
                .bp_table
                .operators_for_category(cat_name)
                .iter()
                .map(|op| (op.label.clone(), op.left_bp))
                .collect();
            let strata = tree.bp_stratification(&bp_map);
            if strata.len() > 1 {
                let lines: Vec<String> = strata
                    .iter()
                    .map(|(bp, reachable, total)| {
                        format!(
                            "BP≤{}: {}/{} rules ({:.0}%)",
                            bp,
                            reachable,
                            total,
                            *reachable as f64 / *total as f64 * 100.0
                        )
                    })
                    .collect();
                pipeline_diagnostic(
                    &bundle.grammar_name,
                    DiagnosticId::D12,
                    "bp-stratification",
                    crate::lint::LintSeverity::Note,
                    format!("category {}: BP stratification: {}", cat_name, lines.join(", "),),
                    None,
                );
            }
        }
    }
    }

    // ── 1.2a: Trie-informed WFST weight scaling ─────────────────────────────
    // Compute trie-informed weight adjustments from decision tree depth/ambiguity
    // and apply them to prediction WFST transition weights. Deeper unique prefixes
    // get lower weight (higher confidence), short shared prefixes get higher weight.
    {
        let dt_trees = decision_trees.trees();
        let trie_weight_adjustments =
            crate::decision_tree::compute_weight_adjustments(dt_trees, &token_id_map);
        for ((cat, token_variant), adjustment) in &trie_weight_adjustments {
            if let Some(wfst) = prediction_wfsts.get_mut(cat.as_str()) {
                wfst.adjust_weight(token_variant, *adjustment);
            }
        }
    }

    // ── 1.2b: Trie+WFST dead-rule confirmation (2nd pass) ──────────────────
    // Now that decision trees are built, re-run dead-rule collection with trie
    // reachability to confirm WfstUnreachable rules. Rules dead in BOTH the
    // WFST and the trie are added to the dead set.
    {
        let dt_trees = decision_trees.trees();
        let confirmed = collect_dead_rule_labels_with_ignored(
            &bundle.rule_infos,
            &bundle.categories,
            &first_sets,
            &prediction_wfsts,
            &bundle.semantic_dependency_groups,
            dt_trees,
            &bundle.rd_rules,
            &bundle.dead_rule_ignore_labels,
        );
        let new_dead: Vec<String> = confirmed
            .difference(&all_dead_rule_labels)
            .cloned()
            .collect();
        if !new_dead.is_empty() {
            let mut sorted: Vec<&str> = new_dead.iter().map(|s| s.as_str()).collect();
            sorted.sort_unstable();
            pipeline_diagnostic(
                &bundle.grammar_name, DiagnosticId::I07, "trie-confirmed-dead",
                crate::lint::LintSeverity::Info,
                format!(
                    "trie-confirmed dead: {} additional rule(s) confirmed dead via trie+WFST cross-validation: [{}]",
                    new_dead.len(), sorted.join(", "),
                ),
                None,
            );
            all_dead_rule_labels.extend(new_dead);
        }
    }

    // ── 1.3a: Trie-depth sync token ranking ─────────────────────────────────
    // Adjust recovery sync token discounts based on trie depth. Sync tokens at
    // trie root (depth 0) are preferred for error recovery; deep tokens are demoted.
    {
        let dt_trees = decision_trees.trees();
        let depth_discounts =
            crate::decision_tree::compute_sync_depth_discounts(dt_trees, &token_id_map);
        if !depth_discounts.is_empty() {
            for rwfst in &mut recovery_wfsts {
                let cat_name = rwfst.category().to_string();
                let mut cat_discounts: std::collections::HashMap<u16, f64> =
                    std::collections::HashMap::new();
                for (&(ref cat, token_id), &discount) in &depth_discounts {
                    if cat == &cat_name {
                        // Merge with existing prediction discounts (multiply)
                        let existing = rwfst.prediction_discount(token_id);
                        cat_discounts.insert(token_id, existing * discount);
                    }
                }
                if !cat_discounts.is_empty() {
                    rwfst.set_prediction_discounts(cat_discounts);
                }
            }
        }
    }

    // ── 1.7a: Trie-pruned NFA spillover refinement ──────────────────────────
    // Refine NFA spillover set using decision tree dispatch strategy.
    // A category marked for NFA spillover by the ad-hoc grouping may actually
    // have disjoint suffixes (resolvable without backtracking) for all its
    // ambiguous tokens. Remove such categories from the spillover set.
    {
        let dt_trees = decision_trees.trees();
        let mut to_remove = Vec::new();
        for cat in &nfa_spillover_categories {
            if let Some(tree) = dt_trees.get(cat) {
                let dispatch_tokens = tree.dispatch_tokens(&token_id_map);
                let all_resolved = dispatch_tokens.iter().all(|token_variant| {
                    match tree.dispatch_strategy(token_variant, &token_id_map) {
                        crate::decision_tree::DispatchStrategy::NotPresent
                        | crate::decision_tree::DispatchStrategy::Singleton { .. }
                        | crate::decision_tree::DispatchStrategy::DisjointSuffix { .. } => true,
                        crate::decision_tree::DispatchStrategy::AmbiguousFanout { .. } => false,
                    }
                });
                if all_resolved {
                    to_remove.push(cat.clone());
                }
            }
        }
        if !to_remove.is_empty() {
            to_remove.sort();
            pipeline_diagnostic(
                &bundle.grammar_name, DiagnosticId::I08, "trie-pruned-nfa-spillover",
                crate::lint::LintSeverity::Info,
                format!(
                    "trie-pruned NFA spillover: removed {} category(ies) with fully disjoint dispatch: [{}]",
                    to_remove.len(),
                    to_remove.join(", "),
                ),
                None,
            );
            for cat in &to_remove {
                nfa_spillover_categories.remove(cat);
            }
        }
    }

    // ── CD06 Phase 4B M1.0 (2026-06-10): MEASURE-FIRST shared-suffix gate ──
    // The would-apply measurement for CD06 right-factoring (A → β a | γ a ⟹
    // A → A' a). Reports the per-grammar shared_suffix_ratio (an UPPER BOUND:
    // last-item bucketing over Terminal/NonTerminal tails). Per the plan's
    // gate, a ratio < ~0.10 on the production grammars STOPS CD06 at
    // diagnostic-only (no suffix-trie codegen) and records the negative.
    //
    // VERDICT (2026-06-11, Phase 4B closed): the measured depth2 ratios
    // EXCEEDED the screen (calculator 0.19, rhocalc 0.42, Ambient 0.57,
    // GuardedRho 0), so the group-level analysis decided instead: every
    // depth-2 bucket's rules are already discriminated by disjoint LEADING
    // literals (CD02 top-down dispatch), so a shared tail is parsed once
    // whether or not it is factored — right-factoring would merge generated
    // CODE (size only) and remove ZERO parse work. CD06 is STOPPED at
    // diagnostic-only; the transform itself is proven meaning-preserving in
    // CD06_SuffixFactor.v (factor_eq_matching_rule = exact match-list
    // equality) should a future grammar show non-disjoint leading dispatch
    // over heavy shared tails.
    {
        let m = crate::decision_tree::measure_shared_nonterminal_suffixes(&bundle.rd_rules);
        pipeline_diagnostic(
            &bundle.grammar_name, DiagnosticId::I17, "cd06-shared-suffix-measure",
            crate::lint::LintSeverity::Info,
            format!(
                "CD06 measure-first: shared_suffix_ratio depth1={:.4} ({}/{}; crude — dominated by shared close delimiters) depth2={:.4} ({}/{}; the would-apply signal; gate ≥0.10 to wire factoring); depth2 groups: [{}]",
                m.ratio_depth1(),
                m.shared_depth1,
                m.eligible,
                m.ratio_depth2(),
                m.shared_depth2,
                m.eligible,
                m.groups_depth2.join("; "),
            ),
            None,
        );
    }

    // ── Sprint 4: Dead-prefix recovery weight penalty ──────────────────────
    // After trie+WFST dead-rule confirmation, detect "dead prefixes" — dispatch
    // tokens whose entire trie subtree leads only to dead rules. Increase their
    // recovery WFST weights (demoting them as recovery targets).
    // Data flow: WFST → Decision Tree → Dead Prefix → Recovery WFST
    {
        let dt_trees = decision_trees.trees();
        let dead_warnings = detect_dead_rules_with_ignored(
            &bundle.rule_infos,
            &bundle.categories,
            &first_sets,
            &prediction_wfsts,
            &bundle.semantic_dependency_groups,
            &nfa_spillover_categories,
            &bundle.rd_rules,
            &bundle.dead_rule_ignore_labels,
        );
        let dead_prefixes = detect_dead_prefixes(&dead_warnings, dt_trees, &token_id_map);
        if !dead_prefixes.is_empty() {
            const DEAD_PREFIX_WEIGHT_PENALTY: f64 = 2.0;
            let mut total_adjusted = 0usize;
            for rwfst in &mut recovery_wfsts {
                let cat_name = rwfst.category().to_string();
                if let Some(prefix_tokens) = dead_prefixes.get(&cat_name) {
                    let mut discounts: std::collections::HashMap<crate::token_id::TokenId, f64> =
                        std::collections::HashMap::new();
                    for token_variant in prefix_tokens {
                        if let Some(token_id) = token_id_map.get(token_variant) {
                            let existing = rwfst.prediction_discount(token_id);
                            // Increase weight = reduce discount (multiply by penalty)
                            discounts.insert(token_id, existing * DEAD_PREFIX_WEIGHT_PENALTY);
                            total_adjusted += 1;
                        }
                    }
                    if !discounts.is_empty() {
                        rwfst.set_prediction_discounts(discounts);
                    }
                }
            }
            if total_adjusted > 0 {
                pipeline_diagnostic(
                    &bundle.grammar_name, DiagnosticId::I09, "dead-prefix-weight-penalty",
                    crate::lint::LintSeverity::Info,
                    format!(
                        "applied dead-prefix weight penalty (×{:.1}) to {} sync token(s) across {} category(ies)",
                        DEAD_PREFIX_WEIGHT_PENALTY, total_adjusted, dead_prefixes.len(),
                    ),
                    None,
                );
            }
        }
    }

    // ── G25: WPDS stack-aware reachability analysis ─────────────────────
    // Build WPDS and run poststar if the gate is enabled and grammar has ≥2 categories.
    // P05: Time the analysis for the pipeline cost report.
    let wpds_start = std::time::Instant::now();
    let wpds_analysis = if optimization_gates.wpds_reachability && bundle.categories.len() >= 2 {
        let wpds_cats: Vec<crate::wpds::WpdsCategoryInfo> = bundle
            .categories
            .iter()
            .map(|c| crate::wpds::WpdsCategoryInfo {
                name: c.name.clone(),
                is_primary: c.is_primary,
            })
            .collect();
        Some(crate::wpds::analyze_wpds_from_bundle(
            &bundle.grammar_name,
            &wpds_cats,
            &bundle.all_syntax,
            &prediction_wfsts,
        ))
    } else {
        // ── D-B02: Lazy analysis skip — WPDS ──────────────────────────────
        if bundle.categories.len() < 2 {
            pipeline_diagnostic(
                &bundle.grammar_name,
                DiagnosticId::I13,
                "lazy-analysis-skip",
                crate::lint::LintSeverity::Info,
                format!(
                    "WPDS analysis skipped: {} category(ies) < 2 threshold",
                    bundle.categories.len(),
                ),
                None,
            );
        }
        None
    };
    let wpds_elapsed = if wpds_analysis.is_some() {
        Some(wpds_start.elapsed())
    } else {
        None
    };

    // ── INT-01: WPDS PredictionWfst weight refinement ─────────────────────
    // For rules with equal WFST weights sharing a dispatch token, use WPDS
    // poststar weights as tiebreaker (lower WPDS weight → lower WFST weight).
    if let Some(ref analysis) = wpds_analysis {
        wpds_refine_prediction_weights(&mut prediction_wfsts, analysis);
    }

    // ── COMP-07: WPDS × Trie dead-rule confirmation ────────────────────
    // Cross-reference WPDS-unreachable rules with decision tree presence.
    let wpds_phantom_entries = if let Some(ref analysis) = wpds_analysis {
        wpds_confirm_trie_dead_rules(&decision_trees, analysis)
    } else {
        Vec::new()
    };

    // ── INT-02: WPDS Decision Tree Dead-Rule Recording ─────────────────
    // Record WPDS-dead rules for downstream codegen suppression. The PathMap
    // trie structure is immutable, but codegen can skip Ambiguous candidates
    // that are WPDS-unreachable.
    let wpds_dead_rule_labels: std::collections::HashSet<String> = wpds_phantom_entries
        .iter()
        .map(|(label, _)| label.clone())
        .collect();
    if !wpds_dead_rule_labels.is_empty() {
        eprintln!(
            "  {}INT-02{}: {} WPDS-dead rules recorded for codegen suppression",
            "\x1b[2m",
            "\x1b[0m",
            wpds_dead_rule_labels.len(),
        );
    }

    // Stage 10.7 (2026-05-05): CEK-4 dead frame computation DELETED.
    // Frame_Cat enum (target of dead-frame elimination) is gone with
    // trampoline.rs (Stage 10.6). Walker uses WPDS stack symbols, not
    // named frame variants — the optimization is structurally subsumed.

    // ── INT-03: WPDS NFA Spillover Reduction ────────────────────────────
    // Remove WPDS-unreachable rules from NFA spillover groups. If a category's
    // spillover is eliminated (all ambiguous groups become singletons), remove
    // it from nfa_spillover_categories.
    if let Some(ref analysis) = wpds_analysis {
        let dead_labels: std::collections::HashSet<&str> = analysis
            .unreachable_rules
            .iter()
            .map(|r| r.rule_label.as_str())
            .collect();
        if !dead_labels.is_empty() {
            let before = nfa_spillover_categories.len();
            nfa_spillover_categories.retain(|cat| {
                // Check if any NFA group in this category still has >1 live rule
                let groups =
                    crate::rd_analysis::group_rd_by_dispatch_token_pub(&bundle.rd_rules, cat);
                groups.iter().any(|(_token, rules)| {
                    let live_count = rules
                        .iter()
                        .filter(|r| !dead_labels.contains(r.label.as_str()))
                        .count();
                    live_count > 1
                })
            });
            let removed = before - nfa_spillover_categories.len();
            if removed > 0 {
                eprintln!(
                    "  {}INT-03{}: eliminated {} NFA spillover categories via WPDS dead-rule removal",
                    "\x1b[2m", "\x1b[0m", removed,
                );
            }
        }
    }

    // ── Mathematical analysis phase ──────────────────────────────────────
    // Feature-gated analyses that produce actionable diagnostics during
    // `language!` macro expansion. Each analysis converts pipeline types
    // to module-internal types, runs analysis, and returns an Option<Result>.
    //
    // ── D-B02: Lazy analysis skip — mathematical analyses ─────────────────
    // Skip expensive mathematical analyses for trivial grammars (< 3 categories)
    // where cross-category interactions are too simple to benefit from them.
    let math_analysis_eligible = bundle.categories.len() >= 3;

    let math_analysis_start = std::time::Instant::now();

    if !math_analysis_eligible {
        pipeline_diagnostic(
            &bundle.grammar_name,
            DiagnosticId::I14,
            "lazy-analysis-skip",
            crate::lint::LintSeverity::Info,
            format!(
                "mathematical analyses skipped: {} category(ies) < 3 threshold",
                bundle.categories.len(),
            ),
            None,
        );
    }

    // ── DB03: Parallel analysis phase execution ──────────────────────────
    // When the parallel_analysis gate is enabled and the grammar is eligible,
    // run all independent mathematical analyses in parallel using
    // `std::thread::scope`. All analysis inputs (bundle.all_syntax,
    // bundle.categories, wpds_analysis) are `Send + Sync` references, so
    // they can be shared across scoped threads without cloning.
    //
    // Dependency structure:
    //   Group A (no WPDS dep): confluence, termination, vpa, wta, petri,
    //     nominal, alternating, provenance, cra, morphism
    //   Group B (WPDS-dependent): safety, cegar, algebraic, ewpds, ara,
    //     ltl, kat
    // Since wpds_analysis is already computed before this point, ALL
    // analyses are independent of each other and can run in parallel.
    //
    // When parallel_analysis is disabled, falls back to sequential execution.
    //
    // Implementation: results are collected into a MathAnalysisResults struct
    // returned from `run_math_analyses_parallel` / `run_math_analyses_sequential`
    // to avoid uninitialized-variable issues with scoped thread closures.

    let (math_results, parallel_phase_count) = if optimization_gates.parallel_analysis
        && math_analysis_eligible
    {
        let r = run_math_analyses_parallel(bundle, wpds_analysis.as_ref());
        let count = r.phase_count;
        (r, count)
    } else {
        (
            run_math_analyses_sequential(bundle, wpds_analysis.as_ref(), math_analysis_eligible),
            0u32,
        )
    };

    // Destructure into individual result bindings for downstream use.
    let confluence_result = math_results.confluence_result;
    let termination_result = math_results.termination_result;
    let vpa_result = math_results.vpa_result;
    let wta_result = math_results.wta_result;
    let safety_result = math_results.safety_result;
    let cegar_result = math_results.cegar_result;
    let algebraic_result = math_results.algebraic_result;
    let ewpds_result = math_results.ewpds_result;
    let ara_result = math_results.ara_result;
    let petri_result = math_results.petri_result;
    let nominal_result = math_results.nominal_result;
    let alternating_result = math_results.alternating_result;
    // OSLF Phase-4 `.1`: bisimulation result threaded into the codegen
    // `AdvancedAnalysisBundle` (N06-ISO / A3 supersede).
    let bisimulation_result = math_results.bisimulation_result;
    // OSLF Phase-6 `.1`: Hindley-Milner base-sort consistency result threaded
    // into the lint `LintContext` (HM01 only — never codegen).
    let hindley_result = math_results.hindley_result;
    let ltl_results = math_results.ltl_results;
    let provenance_result = math_results.provenance_result;
    let cra_result = math_results.cra_result;
    let morphism_result = math_results.morphism_result;
    let kat_result = math_results.kat_result;
    let symbolic_result = math_results.symbolic_result;
    let buchi_result = math_results.buchi_result;
    let mso_result = math_results.mso_result;
    let probabilistic_result = math_results.probabilistic_result;
    let register_result = math_results.register_result;
    let parity_tree_result = math_results.parity_tree_result;
    let multi_tape_result = math_results.multi_tape_result;
    let multiset_result = math_results.multiset_result;
    let two_way_result = math_results.two_way_result;
    let sft_result = math_results.sft_result;
    let egraph_result = math_results.egraph_result;
    let presburger_result = math_results.presburger_result;
    let unification_result = math_results.unification_result;
    let lattice_result = math_results.lattice_result;
    let refinement_analysis = math_results.refinement_analysis;

    let math_analysis_elapsed = math_analysis_start.elapsed();

    // ── DB03: I19 diagnostic — parallel analysis speedup ─────────────────
    if parallel_phase_count > 0 {
        pipeline_diagnostic(
            &bundle.grammar_name,
            DiagnosticId::I19,
            "parallel-analysis",
            crate::lint::LintSeverity::Info,
            format!(
                "DB03 parallel analysis: {} phases executed in parallel ({:.1}ms wall-clock)",
                parallel_phase_count,
                math_analysis_elapsed.as_secs_f64() * 1000.0,
            ),
            Some(format!(
                "gate: optimization_gates.parallel_analysis=true, \
                 eligible: {} categories >= 3",
                bundle.categories.len(),
            )),
        );
    }

    // ── Sprint A2: Wire VPA bracket mismatch tokens into recovery WFSTs ────
    // When VPA analysis finds tokens used as both call and return symbols,
    // InsertToken for those tokens becomes unreliable. Penalize insertion of
    // bracket mismatch tokens with a 2.0× multiplier in all recovery WFSTs.
    if let Some(ref vpa) = vpa_result {
        if !vpa.alphabet_mismatches.is_empty() {
            let mismatch_ids: std::collections::BTreeSet<crate::token_id::TokenId> = vpa
                .alphabet_mismatches
                .iter()
                .filter_map(|name| token_id_map.get(name))
                .collect();
            if !mismatch_ids.is_empty() {
                for rwfst in &mut recovery_wfsts {
                    rwfst.set_bracket_mismatch_ids(mismatch_ids.clone());
                }
                pipeline_diagnostic(
                    &bundle.grammar_name, DiagnosticId::I20, "bracket-mismatch-insert-penalty",
                    crate::lint::LintSeverity::Info,
                    format!(
                        "Sprint A2: applied 2.0× InsertToken penalty for {} bracket mismatch token(s): {}",
                        mismatch_ids.len(),
                        vpa.alphabet_mismatches.join(", "),
                    ),
                    None,
                );
            }
        }
    }

    // ── Sprint C2: Wire Büchi accepting SCC categories into recovery WFSTs ──
    // Categories in accepting SCCs (recursive grammar loops) prefer InsertToken
    // recovery to maintain the loop structure. SkipToSync is penalized because
    // breaking out of a recursive loop is structurally damaging.
    if let Some(ref buchi) = buchi_result {
        if buchi.has_accepting_cycle {
            let scc_cats: HashSet<&str> = buchi
                .accepting_sccs
                .iter()
                .flatten()
                .map(|s| s.as_str())
                .collect();
            let mut count = 0_usize;
            for rwfst in &mut recovery_wfsts {
                if scc_cats.contains(rwfst.category()) {
                    rwfst.set_recursive_category(true);
                    count += 1;
                }
            }
            if count > 0 {
                pipeline_diagnostic(
                    &bundle.grammar_name, DiagnosticId::I21, "liveness-recovery",
                    crate::lint::LintSeverity::Info,
                    format!(
                        "Sprint C2: applied liveness-aware recovery to {} recursive category(ies): {}",
                        count,
                        scc_cats.iter().copied().collect::<Vec<_>>().join(", "),
                    ),
                    None,
                );
            }
        }
    }

    // ── Unified lint layer ─────────────────────────────────────────────────
    // Construct LintContext with all pipeline data and run all lints.
    // Moved after decision tree construction so PathMap-derived lints
    // (G32, D10, W03 cross-category hotspot, etc.) can access decision_trees.
    {
        let dt_trees = decision_trees.trees();
        // Compute dead-rule warnings once for lint caching.
        // This replaces the duplicate detect_dead_rules() call that lint_w01
        // previously performed independently.
        let raw_dead_rule_warnings = crate::pipeline::detect_dead_rules_with_ignored(
            &bundle.rule_infos,
            &bundle.categories,
            &first_sets,
            &prediction_wfsts,
            &bundle.semantic_dependency_groups,
            &nfa_spillover_categories,
            &bundle.rd_rules,
            &bundle.dead_rule_ignore_labels,
        );
        let cached_dead_rule_warnings =
            crate::pipeline::filter_dead_rule_warnings_with_decision_trees(
                raw_dead_rule_warnings,
                dt_trees,
            );

        // Phase 7A.1 (T11/2026-05-05): predicate-dispatch diagnostics.
        // Derives DispatchDiagnostics from a fresh dispatch plan classification
        // so PD-aware lints (D-prefix codes via lint.rs:8593+) surface
        // signature/conflict/cyclic-dispatch information instead of silently
        // no-op'ing on `dispatch_diagnostics: None`.
        let dispatch_plan_for_lints =
            crate::predicate_dispatch::classify_grammar(&bundle.all_syntax, &bundle.categories);
        let dispatch_diagnostics_data = crate::predicate_dispatch::compile_predicate_pipeline(
            &dispatch_plan_for_lints,
            &bundle.all_syntax,
            &bundle.categories,
        );

        let lint_ctx = crate::lint::LintContext {
            grammar_name: &bundle.grammar_name,
            rule_locations: &bundle.rule_locations,
            categories: &bundle.categories,
            rules: &bundle.rule_infos,
            rd_rules: &bundle.rd_rules,
            first_sets: &first_sets,
            follow_sets: &follow_sets,
            bp_table: &bundle.bp_table,
            prediction_wfsts: &prediction_wfsts,
            recovery_wfsts: &recovery_wfsts,
            cast_rules: &bundle.cast_rules,
            cross_rules: &bundle.cross_rules,
            nfa_spillover_categories: &nfa_spillover_categories,
            recovery_config: &bundle.recovery_config,
            all_syntax: &bundle.all_syntax,
            follow_inputs: &bundle.follow_inputs,
            semantic_dependency_groups: &bundle.semantic_dependency_groups,
            pre_collected_diagnostics: &w05_diagnostics,
            decision_trees: dt_trees,
            token_id_map: &token_id_map,
            dead_rule_warnings: &cached_dead_rule_warnings,
            dead_rule_ignore_labels: &bundle.dead_rule_ignore_labels,
            refinement_types: &bundle.refinement_types,
            grammar_profile: Some(&grammar_profile),
            wpds_analysis: wpds_analysis.as_ref(),
            wpds_elapsed,
            // ── Mathematical analysis results ──
            safety_result: safety_result.as_ref(),
            cegar_result: cegar_result.as_ref(),
            algebraic_result: algebraic_result.as_ref(),
            math_analysis_elapsed: Some(math_analysis_elapsed),
            confluence_result: confluence_result.as_ref(),
            termination_result: termination_result.as_ref(),
            vpa_result: vpa_result.as_ref(),
            wta_result: wta_result.as_ref(),
            ewpds_result: ewpds_result.as_ref(),
            ara_result: ara_result.as_ref(),
            petri_result: petri_result.as_ref(),
            nominal_result: nominal_result.as_ref(),
            alternating_result: alternating_result.as_ref(),
            ltl_results: ltl_results.as_ref(),
            provenance_result: provenance_result.as_ref(),
            cra_result: cra_result.as_ref(),
            morphism_result: morphism_result.as_ref(),
            kat_result: kat_result.as_ref(),
            // ── Advanced automata analysis results ──
            symbolic_result: symbolic_result.as_ref(),
            buchi_result: buchi_result.as_ref(),
            mso_result: mso_result.as_ref(),
            probabilistic_result: probabilistic_result.as_ref(),
            register_result: register_result.as_ref(),
            parity_tree_result: parity_tree_result.as_ref(),
            multi_tape_result: multi_tape_result.as_ref(),
            multiset_result: multiset_result.as_ref(),
            two_way_result: two_way_result.as_ref(),
            sft_result: sft_result.as_ref(),
            egraph_result: egraph_result.as_ref(),
            dispatch_diagnostics: Some(&dispatch_diagnostics_data),
            // ── Constraint theory analysis results ──
            presburger_result: presburger_result.as_ref(),
            unification_result: unification_result.as_ref(),
            lattice_result: lattice_result.as_ref(),
            // ── Refinement type analysis results ──
            refinement_analysis: refinement_analysis.as_ref(),
            // ── Hindley-Milner base-sort consistency (OSLF Phase 6 `.1`) ──
            hindley_result: hindley_result.as_ref(),
        };

        // DB04: Use cached lint results when the optimization gate is enabled.
        // If the grammar spec hash matches the cached hash, all lints are skipped.
        #[allow(unused_mut)]
        let mut diagnostics =
            crate::lint::run_lints_cached(&lint_ctx, optimization_gates.cached_lints);

        // ── Repair enrichment ──
        // Scan diagnostics for specific lint codes and append repair suggestions.
        crate::repair::enrich_diagnostics_with_repairs(
            &mut diagnostics,
            confluence_result.as_ref(),
            &bundle.all_syntax,
        );
        crate::repair::enrich_diagnostics_with_morphism_repairs(
            &mut diagnostics,
            morphism_result.as_ref(),
        );

        // ── Proof certificate generation ──
        {
            let _confluence_ref: Option<&crate::confluence::ConfluenceAnalysis> =
                confluence_result.as_ref();
            let _termination_ref: Option<&crate::termination::TerminationResult> =
                termination_result.as_ref();
            let certificates = crate::proof_output::generate_certificates(
                _confluence_ref,
                _termination_ref,
                safety_result.as_ref(),
            );
            if !certificates.is_empty() {
                for cert in &certificates {
                    diagnostics.push(crate::lint::LintDiagnostic {
                        id: DiagnosticId::Z01,
                        name: "proof-certificate",
                        severity: crate::lint::LintSeverity::Note,
                        category: None,
                        rule: None,
                        message: format!(
                            "proof certificate generated: {} ({})",
                            cert.property, cert.verdict,
                        ),
                        hint: None,
                        grammar_name: Some(bundle.grammar_name.clone()),
                        source_location: None,
                    });
                }
            }
        }

        crate::lint::emit_diagnostics_for_grammar(&bundle.grammar_name, &diagnostics);
    }

    // ── A5: Ambiguity targeting analysis ──────────────────────────────────
    // Identify per-token ambiguity for downstream optimizations (B1, buffer
    // pre-sizing). The threshold=1 means any token with >1 alternative is
    // flagged as a candidate for multi-token lookahead.
    {
        let ambiguity_result = crate::cost_benefit::analyze_ambiguity_targets(
            &prediction_wfsts,
            &first_sets,
            1, // threshold: flag tokens with >1 alternative
        );
        if !ambiguity_result.ambiguous_tokens.is_empty() {
            let mut detail_lines: Vec<String> = ambiguity_result
                .ambiguous_tokens
                .iter()
                .map(|info| {
                    format!(
                        "  {}::{} — {} alternative(s): [{}]{}",
                        info.category,
                        info.token,
                        info.alternative_count,
                        info.rule_labels.join(", "),
                        if info.lookahead_candidate {
                            " ← B1 candidate"
                        } else {
                            ""
                        },
                    )
                })
                .collect();
            if !ambiguity_result.presized_categories.is_empty() {
                detail_lines.push(format!(
                    "  NFA spillover pre-sizing: {}",
                    ambiguity_result
                        .presized_categories
                        .iter()
                        .map(|(cat, sz)| format!("{}={}", cat, sz))
                        .collect::<Vec<_>>()
                        .join(", ")
                ));
            }
            pipeline_diagnostic(
                &bundle.grammar_name, DiagnosticId::I07, "ambiguity-targeting",
                crate::lint::LintSeverity::Info,
                format!(
                    "ambiguity targeting: {} ambiguous token(s), {} unambiguous, max ambiguity={}\n{}",
                    ambiguity_result.ambiguous_tokens.len(),
                    ambiguity_result.unambiguous_count,
                    ambiguity_result.max_ambiguity,
                    detail_lines.join("\n"),
                ),
                None,
            );
        }
    }

    // ── D2: Grammar complexity report ─────────────────────────────────
    // Build and emit a unified complexity report that combines per-category
    // WFST metrics, ambiguity analysis, and optimization recommendations.
    // Reuses the grammar_profile computed above for D1 (no duplicate work).
    {
        let composed_entries = complete_weight_map.as_ref().map_or(0, |m| m.len());
        let resolved = composed_resolutions.as_ref().map_or(0, |r| r.len());
        let report = crate::cost_benefit::GrammarComplexityReport::build(
            &bundle.grammar_name,
            &grammar_profile,
            &prediction_wfsts,
            &first_sets,
            composed_entries,
            resolved,
        );
        crate::lint::emit_diagnostic(&report.to_diagnostic());
    }

    // Stage 10.5b conclusion (2026-05-05): write_parser_helpers call DELETED.
    // The emitted helpers (expect_token, expect_ident, peek_token, peek_ahead)
    // were only consumed by trampoline-emitted RD handlers (gone in Stage 10.5).

    // D07: Emit runtime coverage tracking module (always enabled)
    if emit_coverage {
        buf.push_str(
            "mod __coverage { \
                 use std::sync::Mutex; \
                 use std::collections::HashSet; \
                 static COVERED: Mutex<HashSet<(&'static str, u32)>> = Mutex::new(HashSet::new()); \
                 pub fn record(cat: &'static str, path_id: u32) { \
                     if let Ok(mut set) = COVERED.lock() { set.insert((cat, path_id)); } \
                 } \
                 pub fn dump() -> HashSet<(String, u32)> { \
                     COVERED.lock().map(|set| \
                         set.iter().map(|(c, id)| (c.to_string(), *id)).collect() \
                     ).unwrap_or_default() \
                 } \
                 pub fn reset() { \
                     if let Ok(mut set) = COVERED.lock() { set.clear(); } \
                 } \
             } ",
        );

        // D07 diagnostic: report number of instrumented categories
        let instrumented_cats: Vec<&str> = category_names
            .iter()
            .filter_map(|cat_name| {
                decision_trees
                    .get_tree(cat_name)
                    .filter(|tree| tree.stats.total_states > 0)
                    .map(|_| cat_name.as_str())
            })
            .collect();
        if !instrumented_cats.is_empty() {
            pipeline_diagnostic(
                &bundle.grammar_name,
                DiagnosticId::D07,
                "path-coverage-report",
                crate::lint::LintSeverity::Note,
                format!(
                    "{} categories instrumented for coverage tracking: [{}]",
                    instrumented_cats.len(),
                    instrumented_cats.join(", "),
                ),
                Some("call __coverage::dump() to retrieve coverage data".to_string()),
            );
        }
    }

    // BP03: Emit `token_variant_id()` when the gate is enabled and any category has
    // enough operators to benefit from static array lookup.
    if optimization_gates.bp_table_lookup {
        let bp03_needed = bundle.categories.iter().any(|cat| {
            let infix_count = bundle.bp_table.operators_for_category(&cat.name).len();
            let postfix_count = bundle
                .bp_table
                .postfix_operators_for_category(&cat.name)
                .len();
            let mixfix_count = bundle
                .bp_table
                .mixfix_operators_for_category(&cat.name)
                .len();
            // Stage 10.5b conclusion (2026-05-05): BP_TABLE_LOOKUP_THRESHOLD
            // inlined as `8` (BP03 threshold from trampoline.rs era).
            infix_count >= 8 || postfix_count >= 8 || mixfix_count >= 8
        });
        if bp03_needed {
            crate::automata::codegen::write_token_variant_id(
                &mut buf,
                variant_map,
                &bundle.custom_tokens,
            );
        }
    }

    // Stage 10.5 (2026-05-04): trampoline-emission per-category for-loop DELETED.
    // Walker (WPDS) emits `parse_<Cat>_via_wpda` via `wpda_codegen/facade.rs`,
    // subsuming `parse_<cat>_own` and `parse_<cat>_own_traced`. The associated
    // setup blocks (prefix_cse_all, all_frame_infos, unified_mode, TrampolineConfig
    // construction) all died with the loop they fed.

    // Stage 10.5 (2026-05-04): cross-category dispatch emission DELETED.
    // `write_category_dispatch` emitted arms calling `parse_<cat>_own`, which
    // is no longer emitted post-trampoline-deletion. Walker (WPDS) provides
    // equivalent cross-category dispatch via `parse_<Cat>_via_wpda` emitted by
    // `wpda_codegen/facade.rs` (Fork+AmbiguityFanout+lex-min weights).

    // ── Error recovery functions (parallel set, zero overhead on non-recovering path) ──

    // Collect all grammar terminals (raw strings) for sync predicate generation.
    // This determines which structural delimiters (";", ",", etc.) actually exist
    // in the grammar — only those will have corresponding Token variants.
    let grammar_terminals: std::collections::HashSet<String> = {
        let mut terminals = std::collections::HashSet::new();
        for input in &bundle.follow_inputs {
            for t in collect_terminals_recursive(&input.syntax) {
                terminals.insert(t);
            }
        }
        // Structural delimiters (){}[], are always in the terminal set
        for delim in &["(", ")", "{", "}", "[", "]", ","] {
            terminals.insert(delim.to_string());
        }
        // Binder terminals (^ and .) for lambda syntax
        if bundle.has_binders {
            terminals.insert("^".to_string());
            terminals.insert(".".to_string());
            // Dollar terminals for function application syntax
            for cat in &bundle.categories {
                let cat_lower = cat.name.to_lowercase();
                terminals.insert(format!("${}", cat_lower));
                terminals.insert(format!("$${}(", cat_lower));
            }
        }
        terminals
    };

    // Stage 10.5r-d (2026-05-05): per-category recovery emission DELETED.
    // Per Plan agent finding (ac1ca5956a3783d6c): `wfst_recover_<Cat>` was
    // emitted by `generate_wfst_recovery_fn` but had ZERO callers — the
    // actual runtime recovery is the wrapper-level skip-to-sync loop in
    // `wpda_codegen/facade.rs::parse_<Cat>_via_wpda_recovering`. The dead
    // emission chain (generate_wfst_recovery_fn + CROSS_CAT_CASTS_<cat>
    // static + emit_recovery_wfst_static + emit_parse_simulator_static)
    // dragged in FRAME_STATE_<CAT>/RUNNING_WEIGHT_<CAT>/PARENT_WEIGHT_<CAT>
    // thread-local references that no longer have a setter post-trampoline-
    // deletion. Eliminating the dead chain removes the entire identifier
    // surface that was begging for shims. Sync predicates still emitted
    // for facade.rs's wrapper-level use.
    for cat in &bundle.categories {
        let own_follow = follow_sets.get(&cat.name).cloned().unwrap_or_default();

        // Generate sync predicate: is_sync_Cat(token) -> bool
        generate_sync_predicate(&mut buf, &cat.name, &own_follow, &grammar_terminals);
    }

    // Stage 10.4 (2026-05-04): unified trampoline generation block DELETED.
    // Walker (WPDS) subsumes the multi-category mutual-recursion CPS dispatch
    // via per-cursor `BranchCursor`s and `WpdaState::AmbiguityFanout`.
    // `unified_trampoline.rs` and its FrameVariantInfo / UnifiedTrampolineConfig
    // / write_unified_types entry point all deleted in lockstep.

    // Debug dump: write generated parser code to file for inspection (behind
    // the `walker-trace` feature; the env read is compiled out by default).
    trace_diag! {
    if let Ok(dump_dir) = std::env::var("PRATTAIL_DUMP_PARSER") {
        let dir = if dump_dir == "1" {
            ".".to_string()
        } else {
            dump_dir
        };
        let cat_suffix = category_names.join("-");
        let filename = format!("{}/prattail-parser-{}.rs", dir, cat_suffix);
        if let Ok(()) = std::fs::write(&filename, &buf) {
            eprintln!("PraTTaIL: dumped parser code to {}", filename);
        }
    }
    }

    // ── Build PipelineAnalysis from computed data ──────────────────────────
    // Uses all_dead_rule_labels (unconditionally computed) rather than
    // dead_rules (gated by enhanced_dce) so Ascent DCE always has full data.
    // Advanced automata results are passed through for codegen promotion.
    let advanced = AdvancedAnalysisBundle {
        symbolic: symbolic_result.as_ref(),
        alternating: alternating_result.as_ref(),
        bisimulation: bisimulation_result.as_ref(),
        vpa: vpa_result.as_ref(),
        register: register_result.as_ref(),
        probabilistic: probabilistic_result.as_ref(),
        multi_tape: multi_tape_result.as_ref(),
        buchi: buchi_result.as_ref(),
        _phantom: std::marker::PhantomData,
    };
    let analysis = build_pipeline_analysis(
        &all_dead_rule_labels,
        &prediction_wfsts,
        &bundle.categories,
        &bundle.rule_infos,
        decision_trees.trees().clone(),
        &advanced,
    );

    // Layer 10: save scaffolding DELETED 2026-05-12 along with the load
    // scaffolding (see comment near line 2140). The cache will be wired
    // up properly when a future implementation has a real consumer
    // populating `IncrementalState::category_hashes` during codegen.

    // Lint-A cleanup: emit the single consolidated summary line for this
    // grammar at the very end of the pipeline, covering all
    // `emit_diagnostics_for_grammar` calls that were made during the
    // decision-tree pass and the main lint pass.
    crate::lint::finalize_grammar_summary(&bundle.grammar_name);

    (buf, analysis)
}

/// Convert a `SyntaxItemSpec` to an `RDSyntaxItem`.
///
/// Used for converting syntax items when building `RDRuleInfo` from `RuleSpec`.
pub(crate) fn convert_syntax_item_to_rd(item: &SyntaxItemSpec) -> RDSyntaxItem {
    match item {
        SyntaxItemSpec::Terminal(t) => RDSyntaxItem::Terminal(t.clone()),
        SyntaxItemSpec::NonTerminal { category, param_name } => RDSyntaxItem::NonTerminal {
            category: category.clone(),
            param_name: param_name.clone(),
        },
        SyntaxItemSpec::IdentCapture { param_name } => {
            RDSyntaxItem::IdentCapture { param_name: param_name.clone() }
        },
        SyntaxItemSpec::TokenKindCapture { param_name, kind_name } => {
            RDSyntaxItem::TokenKindCapture {
                param_name: param_name.clone(),
                kind_name: kind_name.clone(),
            }
        },
        SyntaxItemSpec::Binder { param_name, category, .. } => RDSyntaxItem::Binder {
            param_name: param_name.clone(),
            binder_category: category.clone(),
        },
        SyntaxItemSpec::Collection {
            param_name,
            element_category,
            separator,
            kind,
            key_val_separator,
        } => RDSyntaxItem::Collection {
            param_name: param_name.clone(),
            element_category: element_category.clone(),
            separator: separator.clone(),
            key_val_separator: key_val_separator.clone(),
            kind: *kind,
        },
        SyntaxItemSpec::Sep { body, separator, kind } => RDSyntaxItem::Sep {
            body: Box::new(convert_syntax_item_to_rd(body)),
            separator: separator.clone(),
            kind: *kind,
        },
        SyntaxItemSpec::Map { body_items } => RDSyntaxItem::Map {
            body_items: body_items.iter().map(convert_syntax_item_to_rd).collect(),
        },
        SyntaxItemSpec::Zip {
            left_name,
            right_name,
            left_category,
            right_category,
            body,
        } => RDSyntaxItem::Zip {
            left_name: left_name.clone(),
            right_name: right_name.clone(),
            left_category: left_category.clone(),
            right_category: right_category.clone(),
            body: Box::new(convert_syntax_item_to_rd(body)),
        },
        SyntaxItemSpec::BinderCollection { param_name, separator } => {
            RDSyntaxItem::BinderCollection {
                param_name: param_name.clone(),
                separator: separator.clone(),
            }
        },
        SyntaxItemSpec::Optional { inner } => RDSyntaxItem::Optional {
            inner: inner.iter().map(convert_syntax_item_to_rd).collect(),
        },
        SyntaxItemSpec::GuardExpression { param_name } => {
            RDSyntaxItem::GuardExpression { param_name: param_name.clone() }
        },
    }
}
