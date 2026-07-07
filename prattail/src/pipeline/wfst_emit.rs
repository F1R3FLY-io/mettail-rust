use super::*;

// ══════════════════════════════════════════════════════════════════════════════
// Generate phase
// ══════════════════════════════════════════════════════════════════════════════

/// Generate lexer code from the lexer bundle, returning the variant map
/// and ambiguity info alongside the generated code string.
///
/// When `hybrid_lexer` is true and the DFA exceeds the direct-coded threshold,
/// AL02 hybrid mode is activated: hot states (BFS depth ≤ 2) are direct-coded
/// while cold states use compressed table lookup.
pub(crate) fn generate_lexer_code_with_map(
    bundle: &LexerBundle,
    hybrid_lexer: bool,
) -> (String, TokenVariantMap, LexerAmbiguityInfo) {
    let mut lexer_input = extract_terminals(
        &bundle.grammar_rules,
        &bundle.type_infos,
        bundle.has_binders,
        &bundle.category_names,
    );
    lexer_input.literal_patterns = bundle.literal_patterns.clone();
    // Enable rational / fixed-point literal handling in the lexer when the
    // corresponding `literal_patterns` maps are populated. Without this, the
    // lexer would skip emission of the rational/fixed-point token arms even
    // though the grammar declares them.
    if !lexer_input.literal_patterns.rational_by_category.is_empty() {
        lexer_input.needs.rational = true;
    }
    if !lexer_input.literal_patterns.fixed_by_category.is_empty() {
        lexer_input.needs.fixed_point = true;
    }
    // If a boolean literal pattern is registered, remove the built-in
    // `True`/`False` keyword terminals so the custom pattern drives matching.
    if bundle.literal_patterns.boolean.is_some() {
        lexer_input.terminals.retain(|t| {
            !matches!(t.kind, crate::automata::TokenKind::True | crate::automata::TokenKind::False)
        });
    }
    lexer_input.custom_tokens = bundle.custom_tokens.clone();
    lexer_input.modes = bundle
        .modes
        .iter()
        .map(|m| crate::lexer::LexerModeInput {
            name: m.name.clone(),
            custom_tokens: m.token_specs.clone(),
        })
        .collect();

    // ── Keyword reservation (PIECE 3) ──────────────────────────────────────
    // Derive the reserved keyword set from the language's reservation policy
    // and the FINAL terminal set (after any boolean-literal-driven True/False
    // removal above, so we never reserve a keyword that is no longer a
    // terminal). The `PRATTAIL_NO_KW_RESERVE` build-time kill-switch forces
    // reservation OFF regardless of policy, giving a byte-identical A/B lever
    // and an emergency rollback path.
    lexer_input.reserved_kinds = if std::env::var_os("PRATTAIL_NO_KW_RESERVE").is_some() {
        crate::automata::ReservedKeywords::none()
    } else {
        bundle.reservation_policy.reserved_kinds(&lexer_input.terminals)
    };

    let (lexer_str, stats) = generate_lexer_as_string_hybrid(&lexer_input, hybrid_lexer);
    (lexer_str, stats.variant_map, stats.ambiguity_info)
}

// ══════════════════════════════════════════════════════════════════════════════
// WFST static embedding (always-on)
// ══════════════════════════════════════════════════════════════════════════════

/// Emit a `PredictionWfst` as CSR-format static arrays with a `LazyLock` constructor.
///
/// For each category with a prediction WFST, generates:
/// ```text
/// static WFST_TRANSITIONS_Cat: &[(u16, u32, f64)] = &[ ... ];
/// static WFST_STATE_OFFSETS_Cat: &[(usize, usize, bool, f64)] = &[ ... ];
/// static WFST_TOKEN_NAMES_Cat: &[&str] = &[ ... ];
/// static WFST_BEAM_WIDTH_Cat: Option<f64> = Some(1.5);  // or None
///
/// static PREDICTION_Cat: std::sync::LazyLock<mettail_prattail::wfst::PredictionWfst> =
///     std::sync::LazyLock::new(|| {
///         mettail_prattail::wfst::PredictionWfst::from_flat(
///             "Cat",
///             WFST_STATE_OFFSETS_Cat,
///             WFST_TRANSITIONS_Cat,
///             WFST_TOKEN_NAMES_Cat,
///             WFST_BEAM_WIDTH_Cat,
///         )
///     });
/// ```
///
/// The `LazyLock` is initialized on first access and persists for the process
/// lifetime. Since the data is entirely `static`, there is no runtime I/O.
pub(crate) fn emit_prediction_wfst_static(
    buf: &mut String,
    prediction_wfsts: &std::collections::HashMap<String, crate::wfst::PredictionWfst>,
) {
    use std::fmt::Write;

    // Iterate prediction_wfsts in sorted category order so the emitted
    // WFST_TRANSITIONS_<Cat> / WFST_STATE_OFFSETS_<Cat> / WFST_TOKEN_NAMES_<Cat>
    // / PREDICTION_<Cat> static blocks land in deterministic positions in
    // the generated source. `HashMap<String, _>` iteration uses a randomized
    // hasher; without sorting, the same grammar produces different
    // `parser.rs` bytes on each build, which defeats the
    // `write_if_changed` short-circuit (macros/src/logic/writer.rs) and
    // forces cargo to invalidate `mettail-languages`'s fingerprint every
    // invocation. Each emitted block is independent — reordering is
    // semantics-preserving.
    let mut sorted_wfsts: Vec<(&String, &crate::wfst::PredictionWfst)> =
        prediction_wfsts.iter().collect();
    sorted_wfsts.sort_by(|a, b| a.0.cmp(b.0));
    for (category, wfst) in sorted_wfsts {
        if wfst.num_actions() == 0 {
            continue;
        }

        // ── Flatten transitions into CSR format ──
        let mut transitions_flat: Vec<(u16, u32, f64)> = Vec::new();
        let mut state_offsets: Vec<(usize, usize, bool, f64)> =
            Vec::with_capacity(wfst.states.len());

        for state in &wfst.states {
            let trans_start = transitions_flat.len();
            let trans_count = state.transitions.len();
            for t in &state.transitions {
                transitions_flat.push((t.input, t.to, t.weight.value()));
            }
            state_offsets.push((
                trans_start,
                trans_count,
                state.is_final,
                state.final_weight.value(),
            ));
        }

        // ── Collect token names from the token map ──
        let mut token_names: Vec<String> = Vec::with_capacity(wfst.token_map.len());
        for i in 0..wfst.token_map.len() {
            if let Some(name) = wfst.token_map.name(i as u16) {
                token_names.push(name.to_string());
            }
        }

        // ── Emit static arrays ──
        // Transitions
        write!(
            buf,
            "#[allow(non_upper_case_globals)] static WFST_TRANSITIONS_{cat}: &[(u16, u32, f64)] = &[",
            cat = category,
        )
        .expect("pipeline: codegen write into in-memory String is infallible");
        for (i, (token_id, target, weight)) in transitions_flat.iter().enumerate() {
            if i > 0 {
                buf.push(',');
            }
            write!(buf, "({}_u16, {}_u32, {})", token_id, target, format_f64(*weight))
                .expect("pipeline: codegen write into in-memory String is infallible");
        }
        buf.push_str("];");

        // State offsets
        write!(
            buf,
            "#[allow(non_upper_case_globals)] static WFST_STATE_OFFSETS_{cat}: &[(usize, usize, bool, f64)] = &[",
            cat = category,
        )
        .expect("pipeline: codegen write into in-memory String is infallible");
        for (i, (start, count, is_final, fw)) in state_offsets.iter().enumerate() {
            if i > 0 {
                buf.push(',');
            }
            write!(buf, "({}_usize, {}_usize, {}, {})", start, count, is_final, format_f64(*fw))
                .expect("pipeline: codegen write into in-memory String is infallible");
        }
        buf.push_str("];");

        // Token names
        write!(
            buf,
            "#[allow(non_upper_case_globals)] static WFST_TOKEN_NAMES_{cat}: &[&str] = &[",
            cat = category,
        )
        .expect("pipeline: codegen write into in-memory String is infallible");
        for (i, name) in token_names.iter().enumerate() {
            if i > 0 {
                buf.push(',');
            }
            write!(buf, "\"{}\"", name)
                .expect("pipeline: codegen write into in-memory String is infallible");
        }
        buf.push_str("];");

        // Beam width
        match wfst.beam_width {
            Some(bw) => write!(
                buf,
                "#[allow(non_upper_case_globals)] static WFST_BEAM_WIDTH_{}: Option<f64> = Some({});",
                category,
                format_f64(bw.value()),
            )
            .expect("pipeline: codegen write into in-memory String is infallible"),
            None => {
                write!(
                    buf,
                    "#[allow(non_upper_case_globals)] static WFST_BEAM_WIDTH_{cat}: Option<f64> = None;",
                    cat = category,
                )
                .expect("pipeline: codegen write into in-memory String is infallible")
            },
        }

        // LazyLock constructor
        write!(buf,
            "#[allow(non_upper_case_globals)] static PREDICTION_{cat}: std::sync::LazyLock<mettail_prattail::wfst::PredictionWfst> = \
             std::sync::LazyLock::new(|| {{ \
                mettail_prattail::wfst::PredictionWfst::from_flat(\
                    \"{cat}\", \
                    WFST_STATE_OFFSETS_{cat}, \
                    WFST_TRANSITIONS_{cat}, \
                    WFST_TOKEN_NAMES_{cat}, \
                    WFST_BEAM_WIDTH_{cat}, \
                ) \
             }});",
            cat = category,
        ).expect("pipeline: codegen write into in-memory String is infallible");
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// WFST recovery static embedding (always-on)
// ══════════════════════════════════════════════════════════════════════════════

/// Emit recovery WFST data as static arrays for runtime context-aware recovery.
///
/// For each category with a recovery WFST, generates:
/// ```text
/// static RECOVERY_SYNC_TOKENS_Cat: &[u16] = &[...];
/// static RECOVERY_SYNC_SOURCES_Cat: &[(u16, u8)] = &[...];
/// static RECOVERY_TOKEN_NAMES_Cat: &[&str] = &[...];
/// ```
///
/// These arrays are consumed by `RecoveryWfst::from_flat()` at runtime when
/// full context-aware recovery is needed (Sprint 4).
// Stage 10.5r-d (2026-05-05): emit_recovery_wfst_static DELETED. Emitted
// RECOVERY_SYNC_TOKENS_<cat>/RECOVERY_SYNC_SOURCES_<cat>/RECOVERY_TOKEN_NAMES_<cat>
// statics consumed only by the now-deleted wfst_recover_<cat> function.

// ══════════════════════════════════════════════════════════════════════════════
// ParseSimulator static embedding (Tier 3 recovery simulation)
// ══════════════════════════════════════════════════════════════════════════════

/// Emit ParseSimulator data as static arrays for runtime Tier 3 recovery simulation.
///
/// Generates per-category FIRST/FOLLOW/infix token ID arrays and a `LazyLock<ParseSimulator>`
/// for context-aware repair rescoring. Only initialized on first access (error path only).
///
/// Generated code:
/// ```text
/// static SIM_FIRST_SETS: &[(&str, &[u16])] = &[("Int", &[3, 7]), ("Bool", &[5])];
/// static SIM_FOLLOW_SETS: &[(&str, &[u16])] = &[("Int", &[1, 2]), ("Bool", &[1])];
/// static SIM_INFIX_SETS: &[(&str, &[u16])] = &[("Int", &[4]), ("Bool", &[])];
/// static PARSE_SIMULATOR: std::sync::LazyLock<ParseSimulator> = std::sync::LazyLock::new(|| {
///     ParseSimulator::from_flat(SIM_FIRST_SETS, SIM_FOLLOW_SETS, SIM_INFIX_SETS, 5)
/// });
/// ```
// Stage 10.5r-d (2026-05-05): emit_parse_simulator_static DELETED. Emitted
// SIM_FIRST_SETS/SIM_FOLLOW_SETS/SIM_INFIX_SETS + PARSE_SIMULATOR LazyLock
// statics consumed only by the now-deleted wfst_recover_<cat> function
// (Tier 3 recovery simulation).

/// Emit a `token_to_id(t: &Token) -> u16` function mapping each Token variant to its TokenId.
///
/// Used by Tier 3 recovery simulation: converts `&[(Token, Range)]` slices to `&[u16]`
/// for `ParseSimulator::simulate_after_repair()`. Only called on error paths.
///
/// Only emits match arms for token variants that actually exist in the grammar's Token enum
/// (filtered by `valid_variants`), avoiding compile errors for non-existent variants.
pub(crate) fn emit_token_to_id_fn(
    buf: &mut String,
    token_id_map: &crate::token_id::TokenIdMap,
    valid_variants: &std::collections::HashSet<String>,
    payload_variants: &std::collections::HashSet<String>,
) {
    use std::fmt::Write;

    buf.push_str("#[allow(dead_code)] fn token_to_id(t: &Token) -> u16 { match t {");

    for (name, id) in token_id_map.iter() {
        // Only emit match arms for variants that exist in the grammar's Token enum
        if !valid_variants.contains(name) {
            continue;
        }

        // Tokens with payloads need wildcard patterns. First check the
        // built-in family via `TokenFamily`; for Other-family variants
        // (custom / category-named tokens like `BigRat`, `Fixed`) consult
        // the `payload_variants` set derived from `CustomTokenSpec`.
        let family = crate::automata::TokenFamily::from_name(name);
        let pattern = if let Some(p) = family.match_pattern() {
            p.to_string()
        } else if payload_variants.contains(name) {
            format!("Token::{}(_)", name)
        } else {
            format!("Token::{}", name)
        };
        write!(buf, "{} => {}_u16,", pattern, id)
            .expect("pipeline: codegen write into in-memory String is infallible");
    }

    // Catch-all for any unmapped variants → use u16::MAX as sentinel
    buf.push_str("_ => u16::MAX,");
    buf.push_str("}}");
}

// Stage 10.5r-d (2026-05-05): WFST recovery codegen DELETED.
// generate_wfst_recovery_fn emitted wfst_recover_<Cat> functions that had
// ZERO callers — they referenced FRAME_STATE_<CAT>/RUNNING_WEIGHT_<CAT>/
// PARENT_WEIGHT_<CAT> thread-locals last set by the deleted trampoline.rs.
// Per Plan agent ac1ca5956a3783d6c: dead code eliminated; recovery now lives
// purely in wpda_codegen/facade.rs::parse_<Cat>_via_wpda_recovering wrapper.

// Stage 10.5 (2026-05-04): `write_trampolined_parser_recovering_wfst` DELETED.
// It emitted `parse_<cat>_own_recovering` calling now-gone `parse_<cat>_own`.
// Walker emits `parse_<Cat>_via_wpda_recovering` via `wpda_codegen/facade.rs`,
// which is what `Cat::parse_recovering` already routes through (atomic swap
// completed in earlier WPDS migration phases). Stage 10.5r migrates the
// recovery-feature wiring (bracket counters, cascade prevention, wfst_recover_<cat>
// invocation) to the Walker codegen path with PDA-stack-based state extraction.

// ══════════════════════════════════════════════════════════════════════════════
// INT-01: WPDS PredictionWfst Weight Refinement
// ══════════════════════════════════════════════════════════════════════════════

/// Refine PredictionWfst dispatch weights using WPDS poststar marginals.
///
/// For rules sharing a dispatch token with equal WFST weights (declaration-order
/// ties), the WPDS category weight is used as tiebreaker: lower WPDS weight
/// (= more reachable in stack context) gets lower WFST dispatch weight.
pub(crate) fn wpds_refine_prediction_weights(
    prediction_wfsts: &mut HashMap<String, crate::wfst::PredictionWfst>,
    analysis: &crate::wpds::WpdsAnalysis,
) {
    use crate::automata::semiring::TropicalWeight;

    for (cat, wfst) in prediction_wfsts.iter_mut() {
        // Only refine if WPDS has weight data for this category's rules
        if analysis.category_weights.is_empty() {
            continue;
        }

        // Group actions by their dispatch token to find ties
        let mut token_groups: HashMap<String, Vec<usize>> = HashMap::new();
        for (idx, action) in wfst.actions.iter().enumerate() {
            let label = action.action.rule_label();
            token_groups.entry(label).or_default().push(idx);
        }

        // For each group of actions with the same weight, use WPDS weights as tiebreaker
        let mut modified = false;
        for action_indices in token_groups.values() {
            if action_indices.len() < 2 {
                continue;
            }
            // Check if all have equal weights (a tie)
            let first_weight = wfst.actions[action_indices[0]].weight;
            let all_equal = action_indices
                .iter()
                .all(|&idx| wfst.actions[idx].weight == first_weight);
            if !all_equal {
                continue;
            }

            // Use WPDS category weight as tiebreaker
            // Lower category weight → rule is "closer" to reachable root → lower dispatch weight
            let cat_weight = analysis
                .category_weights
                .get(cat)
                .copied()
                .unwrap_or(f64::INFINITY);
            if cat_weight.is_finite() && cat_weight > 0.0 {
                // Apply a small tiebreaker offset based on WPDS weight
                for (rank, &idx) in action_indices.iter().enumerate() {
                    let offset = (rank as f64) * 0.001;
                    wfst.actions[idx].weight = TropicalWeight::new(first_weight.value() + offset);
                }
                modified = true;
            }
        }

        if modified {
            eprintln!(
                "  {}INT-01{}: refined WFST weights for `{}` using WPDS marginals",
                "\x1b[2m", "\x1b[0m", cat,
            );
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// COMP-07: WPDS × Trie Dead-Rule Confirmation
// ══════════════════════════════════════════════════════════════════════════════

/// Cross-reference WPDS-unreachable rules with decision tree presence.
///
/// Returns `(rule_label, category)` pairs for rules that are WPDS-dead but
/// still present in a decision tree (phantom entries). These are candidates
/// for INT-02 pruning.
pub(crate) fn wpds_confirm_trie_dead_rules(
    decision_trees: &crate::decision_tree::DecisionTreeBuilder,
    analysis: &crate::wpds::WpdsAnalysis,
) -> Vec<(String, String)> {
    let dt_trees = decision_trees.trees();
    let mut phantom_entries = Vec::new();

    for unreachable in &analysis.unreachable_rules {
        if let Some(tree) = dt_trees.get(&unreachable.category) {
            // Check if this rule label appears in any segment of the decision tree
            let rule_in_tree = tree.segments.iter().any(|segment| {
                segment.iter().any(|(_path, action)| {
                    action.rule_labels().any(|l| l == unreachable.rule_label)
                })
            });
            if rule_in_tree {
                phantom_entries
                    .push((unreachable.rule_label.clone(), unreachable.category.clone()));
            }
        }
    }

    if !phantom_entries.is_empty() {
        eprintln!(
            "  {}COMP-07{}: {} WPDS-dead rules confirmed in decision trees (phantom entries)",
            "\x1b[2m",
            "\x1b[0m",
            phantom_entries.len(),
        );
    }

    phantom_entries
}
