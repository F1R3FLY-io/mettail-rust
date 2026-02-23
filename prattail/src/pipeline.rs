//! Pipeline for lexer+parser code generation.
//!
//! Implements a state machine that:
//! 1. **Extracts** data bundles from `&LanguageSpec`
//! 2. **Generates** lexer and parser code (sequentially)
//! 3. **Finalizes** by concatenating both code strings and parsing into a `TokenStream`
//!
//! This architecture cleanly separates data extraction from code generation,
//! and isolates `!Send` `LanguageSpec` (which contains `proc_macro2::TokenStream`
//! fields) from the generation phase. The Send+Sync bundles enable future
//! parallelism if workload becomes large enough to justify thread overhead.
//!
//! ```text
//! LanguageSpec ──→ [Extract] ──→ Ready ──→ [Generate] ──→ Generated ──→ [Finalize] ──→ Complete
//!                  separate        LexerBundle ──→ lexer_code    concatenate + parse
//!                  bundles         ParserBundle ──→ parser_code   into TokenStream
//! ```

use std::collections::BTreeMap;

use proc_macro2::TokenStream;

use crate::binding_power::{analyze_binding_powers, BindingPowerTable, InfixRuleInfo, MixfixPart};
use crate::dispatch::{
    categories_needing_dispatch, write_category_dispatch, CastRule, CrossCategoryRule,
};
use crate::lexer::{extract_terminals, generate_lexer_as_string, GrammarRuleInfo, TypeInfo};
use crate::pratt::{
    write_dispatch_recovering, write_parser_helpers, write_recovery_helpers, PrefixHandler,
};
use crate::prediction::{
    analyze_cross_category_overlaps, compute_first_sets, compute_follow_sets_from_inputs,
    detect_grammar_warnings, generate_sync_predicate, FirstItem, FollowSetInput, RuleInfo,
};
use crate::recursive::{
    write_dollar_handlers, write_lambda_handlers, write_rd_handler, RDRuleInfo, RDSyntaxItem,
};
use crate::trampoline::{
    write_trampolined_parser, write_trampolined_parser_recovering, TrampolineConfig,
};
use crate::{LanguageSpec, SyntaxItemSpec};

// ══════════════════════════════════════════════════════════════════════════════
// Data bundles — all Send+Sync
// ══════════════════════════════════════════════════════════════════════════════

/// All data needed by the lexer pipeline. Send+Sync.
pub struct LexerBundle {
    grammar_rules: Vec<GrammarRuleInfo>,
    type_infos: Vec<TypeInfo>,
    /// Whether the grammar has binder rules (^x.{body} lambda syntax).
    has_binders: bool,
    /// Category names (needed for dollar terminal generation when has_binders).
    category_names: Vec<String>,
}

/// Category metadata for the parser pipeline. Send+Sync.
pub(crate) struct CategoryInfo {
    pub(crate) name: String,
    pub(crate) native_type: Option<String>,
    pub(crate) is_primary: bool,
}

/// All data needed by the parser pipeline. Send+Sync.
pub struct ParserBundle {
    pub(crate) categories: Vec<CategoryInfo>,
    pub(crate) bp_table: BindingPowerTable,
    pub(crate) rule_infos: Vec<RuleInfo>,
    pub(crate) follow_inputs: Vec<FollowSetInput>,
    pub(crate) rd_rules: Vec<RDRuleInfo>,
    pub(crate) cross_rules: Vec<CrossCategoryRule>,
    pub(crate) cast_rules: Vec<CastRule>,
    /// Whether the grammar has binder rules (^x.{body} lambda syntax).
    pub(crate) has_binders: bool,
    /// Beam width configuration for WFST prediction pruning (feature-gated).
    pub(crate) beam_width: crate::BeamWidthConfig,
    /// Dispatch strategy (unresolved — resolution requires FIRST-set and overlap data).
    pub(crate) dispatch_strategy: crate::DispatchStrategy,
}

// ══════════════════════════════════════════════════════════════════════════════
// Pipeline state machine
// ══════════════════════════════════════════════════════════════════════════════

/// Pipeline state machine for parallel code generation.
///
/// Each state holds the data needed for the next transition.
// Compile-time state machine with 3 total moves — never stored in collections.
#[allow(clippy::large_enum_variant)]
pub enum PipelineState {
    /// Bundles extracted, ready for parallel codegen.
    Ready {
        lexer_bundle: LexerBundle,
        parser_bundle: ParserBundle,
    },
    /// Both code strings generated, ready to merge.
    Generated { lexer_code: String, parser_code: String },
    /// Final output produced.
    Complete(TokenStream),
}

impl PipelineState {
    /// Advance the pipeline to the next state.
    ///
    /// - `Ready → Generated`: runs lexer and parser codegen sequentially
    /// - `Generated → Complete`: concatenates code strings and parses into `TokenStream`
    /// - `Complete → panic`: pipeline is already done
    pub fn advance(self) -> Self {
        match self {
            PipelineState::Ready { lexer_bundle, parser_bundle } => {
                let lexer_code = generate_lexer_code(&lexer_bundle);
                let parser_code = generate_parser_code(&parser_bundle);
                PipelineState::Generated { lexer_code, parser_code }
            },
            PipelineState::Generated { lexer_code, parser_code } => {
                let mut combined = lexer_code;
                combined.push_str(&parser_code);
                let ts = combined
                    .parse::<TokenStream>()
                    .expect("PraTTaIL pipeline: generated code failed to parse as TokenStream");
                PipelineState::Complete(ts)
            },
            PipelineState::Complete(_) => panic!("Pipeline already complete"),
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Entry point
// ══════════════════════════════════════════════════════════════════════════════

/// Run the full pipeline: extract → generate (parallel) → finalize.
///
/// This is the main entry point for parallel code generation. It:
/// 1. Extracts Send+Sync bundles from `&LanguageSpec` on the current thread
/// 2. Runs lexer and parser codegen in parallel via `rayon::join`
/// 3. Concatenates results and parses into a single `TokenStream`
pub fn run_pipeline(spec: &LanguageSpec) -> TokenStream {
    let (lexer_bundle, parser_bundle) = extract_from_spec(spec);

    // Run grammar warning detection and emit to stderr (standard for proc-macro diagnostics)
    let category_names: Vec<String> = spec.types.iter().map(|t| t.name.clone()).collect();
    let all_syntax: Vec<(String, String, Vec<SyntaxItemSpec>)> = spec
        .rules
        .iter()
        .map(|r| (r.label.clone(), r.category.clone(), r.syntax.clone()))
        .collect();
    let warnings = detect_grammar_warnings(&parser_bundle.rule_infos, &category_names, &all_syntax);
    for warning in &warnings {
        eprintln!("warning: {}", warning);
    }

    // EBNF debug dump (opt-in via environment variable)
    if let Ok(dump_target) = std::env::var("PRATTAIL_DUMP_EBNF") {
        let ebnf = crate::ebnf::format_ebnf(spec, &parser_bundle);
        crate::ebnf::write_ebnf_output(&ebnf, &spec.name, &dump_target);
    }

    let mut state = PipelineState::Ready { lexer_bundle, parser_bundle };
    loop {
        state = state.advance();
        if let PipelineState::Complete(ts) = state {
            return ts;
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Extract phase (main thread)
// ══════════════════════════════════════════════════════════════════════════════

/// Extract Send+Sync data bundles from the language specification.
///
/// Single pass over `spec.rules` builds all collections needed by both
/// the lexer and parser pipelines. The `rust_code: Option<TokenStream>`
/// field on `RuleSpec` is intentionally not copied — it is never used
/// by the recursive descent handler generator.
fn extract_from_spec(spec: &LanguageSpec) -> (LexerBundle, ParserBundle) {
    // ── Lexer bundle ──
    let grammar_rules: Vec<GrammarRuleInfo> = spec
        .rules
        .iter()
        .map(|r| GrammarRuleInfo {
            label: r.label.clone(),
            category: r.category.clone(),
            terminals: collect_terminals_recursive(&r.syntax),
            is_infix: r.is_infix,
        })
        .collect();

    let type_infos: Vec<TypeInfo> = spec
        .types
        .iter()
        .map(|t| TypeInfo {
            name: t.name.clone(),
            language_name: spec.name.clone(),
            native_type_name: t.native_type.clone(),
        })
        .collect();

    let has_binders = spec
        .rules
        .iter()
        .any(|r| r.has_binder || r.has_multi_binder);

    let lexer_category_names: Vec<String> = spec.types.iter().map(|t| t.name.clone()).collect();
    let lexer_bundle = LexerBundle {
        grammar_rules,
        type_infos,
        has_binders,
        category_names: lexer_category_names,
    };

    // ── Parser bundle ──
    let categories: Vec<CategoryInfo> = spec
        .types
        .iter()
        .enumerate()
        .map(|(i, t)| CategoryInfo {
            name: t.name.clone(),
            native_type: t.native_type.clone(),
            is_primary: i == 0,
        })
        .collect();

    let category_names: Vec<String> = categories.iter().map(|c| c.name.clone()).collect();

    // Extract infix rules and compute BP table
    let infix_rules: Vec<InfixRuleInfo> = spec
        .rules
        .iter()
        .filter(|r| r.is_infix)
        .map(|r| {
            let (is_mixfix, mixfix_parts) = extract_mixfix_parts(&r.syntax);
            InfixRuleInfo {
                label: r.label.clone(),
                terminal: r
                    .syntax
                    .iter()
                    .find_map(|item| {
                        if let SyntaxItemSpec::Terminal(t) = item {
                            Some(t.clone())
                        } else {
                            None
                        }
                    })
                    .unwrap_or_default(),
                category: r.category.clone(),
                result_category: r.category.clone(),
                associativity: r.associativity,
                is_cross_category: r.is_cross_category,
                is_postfix: r.is_postfix,
                is_mixfix,
                mixfix_parts,
            }
        })
        .collect();

    let bp_table = analyze_binding_powers(&infix_rules);

    // Compute max infix bp per category (exclude postfix) for prefix_bp
    let max_infix_bp: BTreeMap<String, u8> = {
        let mut map = BTreeMap::new();
        for op in &bp_table.operators {
            if op.is_postfix {
                continue;
            }
            let max = map.entry(op.category.clone()).or_insert(0u8);
            *max = (*max).max(op.left_bp).max(op.right_bp);
        }
        map
    };

    // Extract rule_infos for FIRST set computation
    let rule_infos: Vec<RuleInfo> = spec
        .rules
        .iter()
        .map(|r| RuleInfo {
            label: r.label.clone(),
            category: r.category.clone(),
            first_items: r
                .syntax
                .iter()
                .take(1)
                .map(|item| match item {
                    SyntaxItemSpec::Terminal(t) => FirstItem::Terminal(t.clone()),
                    SyntaxItemSpec::NonTerminal { category, .. } => {
                        if category_names.contains(category) {
                            FirstItem::NonTerminal(category.clone())
                        } else {
                            FirstItem::Ident
                        }
                    },
                    SyntaxItemSpec::IdentCapture { .. }
                    | SyntaxItemSpec::Binder { .. }
                    | SyntaxItemSpec::Collection { .. }
                    | SyntaxItemSpec::ZipMapSep { .. }
                    | SyntaxItemSpec::Optional { .. } => FirstItem::Ident,
                })
                .collect(),
            is_infix: r.is_infix,
            is_var: r.is_var,
            is_literal: r.is_literal,
            is_cross_category: r.is_cross_category,
            is_cast: r.is_cast,
        })
        .collect();

    // Extract follow inputs (only category + syntax needed)
    let follow_inputs: Vec<FollowSetInput> = spec
        .rules
        .iter()
        .map(|r| FollowSetInput {
            category: r.category.clone(),
            syntax: r.syntax.clone(),
        })
        .collect();

    // Extract RD rules (without rust_code — it's never used by write_rd_handler)
    let rd_rules: Vec<RDRuleInfo> = spec
        .rules
        .iter()
        .filter(|r| !r.is_infix && !r.is_var && !r.is_literal)
        .map(|rule| {
            let prefix_bp = if rule.is_unary_prefix {
                if let Some(explicit_bp) = rule.prefix_precedence {
                    Some(explicit_bp)
                } else {
                    let cat_max = max_infix_bp.get(&rule.category).copied().unwrap_or(0);
                    Some(cat_max + 2)
                }
            } else {
                None
            };

            RDRuleInfo {
                label: rule.label.clone(),
                category: rule.category.clone(),
                items: rule.syntax.iter().map(convert_syntax_item_to_rd).collect(),
                has_binder: rule.has_binder,
                has_multi_binder: rule.has_multi_binder,
                is_collection: rule.is_collection,
                collection_type: rule.collection_type,
                separator: rule.separator.clone(),
                prefix_bp,
                eval_mode: rule.eval_mode.clone(),
            }
        })
        .collect();

    // Extract cross-category rules
    let cross_rules: Vec<CrossCategoryRule> = spec
        .rules
        .iter()
        .filter(|r| r.is_cross_category)
        .map(|r| CrossCategoryRule {
            label: r.label.clone(),
            source_category: r.cross_source_category.clone().unwrap_or_default(),
            result_category: r.category.clone(),
            operator: r
                .syntax
                .iter()
                .find_map(|item| {
                    if let SyntaxItemSpec::Terminal(t) = item {
                        Some(t.clone())
                    } else {
                        None
                    }
                })
                .unwrap_or_default(),
            needs_backtrack: false,
        })
        .collect();

    // Extract cast rules
    let cast_rules: Vec<CastRule> = spec
        .rules
        .iter()
        .filter(|r| r.is_cast)
        .map(|r| CastRule {
            label: r.label.clone(),
            source_category: r.cast_source_category.clone().unwrap_or_default(),
            target_category: r.category.clone(),
        })
        .collect();

    let parser_bundle = ParserBundle {
        categories,
        bp_table,
        rule_infos,
        follow_inputs,
        rd_rules,
        cross_rules,
        cast_rules,
        has_binders,
        beam_width: spec.beam_width.clone(),
        dispatch_strategy: spec.dispatch_strategy.clone(),
    };

    (lexer_bundle, parser_bundle)
}

// ══════════════════════════════════════════════════════════════════════════════
// Generate phase (parallel via rayon::join)
// ══════════════════════════════════════════════════════════════════════════════

/// Generate lexer code from the lexer bundle.
///
/// Runs the full automata pipeline: terminal extraction → NFA → DFA → minimize → codegen.
fn generate_lexer_code(bundle: &LexerBundle) -> String {
    let lexer_input = extract_terminals(
        &bundle.grammar_rules,
        &bundle.type_infos,
        bundle.has_binders,
        &bundle.category_names,
    );
    let (lexer_str, _stats) = generate_lexer_as_string(&lexer_input);
    lexer_str
}

/// Generate parser code from the parser bundle.
///
/// Runs: FIRST/FOLLOW sets → RD handlers → Pratt parsers → cross-category dispatch.
fn generate_parser_code(bundle: &ParserBundle) -> String {
    let category_names: Vec<String> = bundle.categories.iter().map(|c| c.name.clone()).collect();
    let primary_category = category_names.first().map(|s| s.as_str()).unwrap_or("");

    // Compute FIRST sets
    let mut first_sets = compute_first_sets(&bundle.rule_infos, &category_names);

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
                    _ => {},
                }
            }
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

    // Compute FOLLOW sets from extracted inputs
    let follow_sets = compute_follow_sets_from_inputs(
        &bundle.follow_inputs,
        &category_names,
        &first_sets,
        primary_category,
    );

    // ── Dispatch strategy resolution ─────────────────────────────────────
    // Resolve Auto → Static or Weighted based on grammar metrics.
    // Must happen after overlap analysis (needed for ambiguous_overlap_count).
    #[cfg(feature = "wfst")]
    let use_wfst = {
        let ambiguous_count = overlaps
            .values()
            .filter(|o| !o.ambiguous_tokens.tokens.is_empty())
            .count();
        let resolved = bundle.dispatch_strategy.resolve(
            bundle.rule_infos.len(),
            bundle.cross_rules.len(),
            ambiguous_count,
        );
        resolved == crate::DispatchStrategy::Weighted
    };

    // ── WFST construction (feature-gated + dispatch-gated) ────────────────
    // Build prediction WFSTs and recovery WFSTs from FIRST/FOLLOW/overlap data.
    // These are consulted by weighted dispatch and recovery codegen below.
    // Only constructed when the resolved dispatch strategy is Weighted.
    #[cfg(feature = "wfst")]
    let (prediction_wfsts, recovery_wfsts, _token_id_map) = if use_wfst {
        use crate::prediction::build_dispatch_action_tables;
        use crate::recovery::build_recovery_wfsts;
        use crate::token_id::TokenIdMap;
        use crate::wfst::build_prediction_wfsts;

        // Build native type map for dispatch action table extraction
        let native_types: std::collections::BTreeMap<String, Option<String>> = bundle
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

        // Apply beam width configuration
        if let Some(beam_value) = bundle.beam_width.to_option() {
            let beam = crate::automata::semiring::TropicalWeight::new(beam_value);
            for wfst in prediction_wfsts.values_mut() {
                wfst.set_beam_width(Some(beam));
            }
        }

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
        let grammar_terminals_wfst: std::collections::BTreeSet<String> = {
            let mut terminals = std::collections::BTreeSet::new();
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
        let recovery_wfsts = build_recovery_wfsts(
            &category_names,
            &follow_sets,
            &grammar_terminals_wfst,
            &token_id_map,
        );

        (prediction_wfsts, recovery_wfsts, token_id_map)
    } else {
        // Static dispatch: no WFST construction needed.
        // Empty maps cause all downstream .get() calls to return None,
        // naturally falling through to the static path.
        (
            std::collections::BTreeMap::new(),
            Vec::new(),
            crate::token_id::TokenIdMap::from_names(std::iter::empty()),
        )
    };

    // ── WFST static embedding (feature-gated) ─────────────────────────────
    // Emit prediction WFSTs as CSR-format static arrays with LazyLock constructors.
    // This makes the WFST data available at runtime for dynamic prediction
    // (e.g., with trained model weights overriding heuristic weights).
    let mut buf = String::with_capacity(8192);
    #[cfg(feature = "wfst")]
    {
        emit_prediction_wfst_static(&mut buf, &prediction_wfsts);
        emit_recovery_wfst_static(&mut buf, &recovery_wfsts);
    }

    // Generate RD handlers
    let mut all_prefix_handlers: Vec<PrefixHandler> = Vec::with_capacity(bundle.rd_rules.len());

    for rd_rule in &bundle.rd_rules {
        let handler = write_rd_handler(&mut buf, rd_rule);
        all_prefix_handlers.push(handler);
    }

    // Generate lambda handlers for primary category if grammar has binders
    if bundle.has_binders {
        let lambda_handlers = write_lambda_handlers(&mut buf, primary_category, &category_names);
        all_prefix_handlers.extend(lambda_handlers);

        // Generate dollar-syntax handlers ($proc, $name, etc.) for function application
        let dollar_handlers = write_dollar_handlers(&mut buf, primary_category, &category_names);
        all_prefix_handlers.extend(dollar_handlers);
    }

    // Determine dispatch categories
    let dispatch_categories = categories_needing_dispatch(&bundle.cross_rules, &bundle.cast_rules);

    // Write parser helpers
    write_parser_helpers(&mut buf);

    // Write trampolined parsers per category (stack-safe via explicit continuation stack)
    for cat in &bundle.categories {
        let has_infix = !bundle.bp_table.operators_for_category(&cat.name).is_empty();
        let has_postfix = !bundle
            .bp_table
            .postfix_operators_for_category(&cat.name)
            .is_empty();
        let has_mixfix = !bundle
            .bp_table
            .mixfix_operators_for_category(&cat.name)
            .is_empty();
        let needs_dispatch = dispatch_categories.contains(&cat.name);

        let cat_cast_rules: Vec<CastRule> = bundle
            .cast_rules
            .iter()
            .filter(|r| r.target_category == cat.name)
            .cloned()
            .collect();

        let own_first = first_sets.get(&cat.name).cloned().unwrap_or_default();
        let own_follow = follow_sets.get(&cat.name).cloned().unwrap_or_default();

        let tramp_config = TrampolineConfig {
            category: cat.name.clone(),
            is_primary: cat.is_primary,
            has_infix,
            has_postfix,
            has_mixfix,
            all_categories: category_names.clone(),
            needs_dispatch,
            native_type: cat.native_type.clone(),
            cast_rules: cat_cast_rules,
            own_first_set: own_first,
            all_first_sets: first_sets.clone(),
            follow_set: own_follow,
            has_binders: bundle.has_binders,
            #[cfg(feature = "wfst")]
            prediction_wfst: prediction_wfsts.get(&cat.name).cloned(),
        };

        let cat_handlers: Vec<PrefixHandler> = all_prefix_handlers
            .iter()
            .filter(|h| h.category == cat.name)
            .cloned()
            .collect();

        write_trampolined_parser(
            &mut buf,
            &tramp_config,
            &bundle.bp_table,
            &cat_handlers,
            &bundle.rd_rules,
        );
    }

    // Write cross-category dispatch
    for cat in &bundle.categories {
        let cat_cross: Vec<CrossCategoryRule> = bundle
            .cross_rules
            .iter()
            .filter(|r| r.result_category == cat.name)
            .cloned()
            .collect();
        if cat_cross.is_empty() {
            continue;
        }

        // Use WFST-weighted dispatch when a prediction WFST is available
        #[cfg(feature = "wfst")]
        let used_weighted = {
            if let Some(wfst) = prediction_wfsts.get(&cat.name) {
                crate::dispatch::write_category_dispatch_weighted(
                    &mut buf,
                    &cat.name,
                    &cat_cross,
                    &[],
                    &overlaps,
                    &first_sets,
                    wfst,
                );
                true
            } else {
                false
            }
        };
        #[cfg(not(feature = "wfst"))]
        let used_weighted = false;

        if !used_weighted {
            write_category_dispatch(&mut buf, &cat.name, &cat_cross, &[], &overlaps, &first_sets);
        }
    }

    // ── Error recovery functions (parallel set, zero overhead on non-recovering path) ──

    // Collect all grammar terminals (raw strings) for sync predicate generation.
    // This determines which structural delimiters (";", ",", etc.) actually exist
    // in the grammar — only those will have corresponding Token variants.
    let grammar_terminals: std::collections::BTreeSet<String> = {
        let mut terminals = std::collections::BTreeSet::new();
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

    // Write recovery helpers (once)
    write_recovery_helpers(&mut buf);

    // Write sync predicates and recovering parsers per category
    for cat in &bundle.categories {
        let own_follow = follow_sets.get(&cat.name).cloned().unwrap_or_default();

        // Generate sync predicate: is_sync_Cat(token) -> bool
        generate_sync_predicate(&mut buf, &cat.name, &own_follow, &grammar_terminals);

        let needs_dispatch = dispatch_categories.contains(&cat.name);

        let tramp_config = TrampolineConfig {
            category: cat.name.clone(),
            is_primary: cat.is_primary,
            has_infix: !bundle.bp_table.operators_for_category(&cat.name).is_empty(),
            has_postfix: !bundle
                .bp_table
                .postfix_operators_for_category(&cat.name)
                .is_empty(),
            has_mixfix: !bundle
                .bp_table
                .mixfix_operators_for_category(&cat.name)
                .is_empty(),
            all_categories: category_names.clone(),
            needs_dispatch,
            native_type: cat.native_type.clone(),
            cast_rules: bundle
                .cast_rules
                .iter()
                .filter(|r| r.target_category == cat.name)
                .cloned()
                .collect(),
            own_first_set: first_sets.get(&cat.name).cloned().unwrap_or_default(),
            all_first_sets: first_sets.clone(),
            follow_set: own_follow,
            has_binders: bundle.has_binders,
            #[cfg(feature = "wfst")]
            prediction_wfst: None, // Recovery wrappers don't need weighted dispatch
        };

        // Generate WFST-based recovery function when wfst feature is enabled.
        // This generates a weighted recovery helper that evaluates skip, delete,
        // and substitute strategies — replacing the linear sync_to() scan.
        #[cfg(feature = "wfst")]
        {
            if let Some(recovery_wfst) = recovery_wfsts.iter().find(|w| w.category() == cat.name) {
                generate_wfst_recovery_fn(&mut buf, &cat.name, recovery_wfst);
            }
        }

        // Generate recovering trampolined parser (wraps fail-fast trampoline with error catch)
        #[cfg(feature = "wfst")]
        {
            // Use WFST recovery when available
            if recovery_wfsts.iter().any(|w| w.category() == cat.name) {
                write_trampolined_parser_recovering_wfst(&mut buf, &tramp_config);
            } else {
                write_trampolined_parser_recovering(
                    &mut buf,
                    &tramp_config,
                    &bundle.bp_table,
                    &crate::trampoline::FrameInfo {
                        enum_name: format!("Frame_{}", cat.name),
                        variants: Vec::new(),
                    },
                );
            }
        }
        #[cfg(not(feature = "wfst"))]
        write_trampolined_parser_recovering(
            &mut buf,
            &tramp_config,
            &bundle.bp_table,
            &crate::trampoline::FrameInfo {
                enum_name: format!("Frame_{}", cat.name),
                variants: Vec::new(),
            },
        );

        // Generate recovering dispatch wrapper if needed
        if needs_dispatch {
            write_dispatch_recovering(&mut buf, &cat.name);
        }
    }

    // Debug dump: write generated parser code to file for inspection
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

    buf
}

// ══════════════════════════════════════════════════════════════════════════════
// Helper functions (moved from lib.rs — only used by the pipeline)
// ══════════════════════════════════════════════════════════════════════════════

/// Capitalize the first letter of a string.
fn capitalize_first(s: &str) -> String {
    let mut chars = s.chars();
    match chars.next() {
        None => String::new(),
        Some(first) => {
            let mut result = String::with_capacity(s.len());
            result.extend(first.to_uppercase());
            result.extend(chars);
            result
        },
    }
}

/// Recursively collect all terminal strings from a list of syntax items.
///
/// This extracts terminals from top-level items AND from nested structures
/// like `ZipMapSep` body items and separators.
fn collect_terminals_recursive(items: &[SyntaxItemSpec]) -> Vec<String> {
    let mut terminals = Vec::new();
    for item in items {
        match item {
            SyntaxItemSpec::Terminal(t) => terminals.push(t.clone()),
            SyntaxItemSpec::Collection { separator, .. } => {
                terminals.push(separator.clone());
            },
            SyntaxItemSpec::ZipMapSep { body_items, separator, .. } => {
                terminals.extend(collect_terminals_recursive(body_items));
                terminals.push(separator.clone());
            },
            SyntaxItemSpec::Optional { inner } => {
                terminals.extend(collect_terminals_recursive(inner));
            },
            _ => {},
        }
    }
    terminals.sort();
    terminals.dedup();
    terminals
}

/// Detect whether an infix rule is mixfix and extract its parts.
///
/// A rule is mixfix if its syntax pattern has 3+ operands (NonTerminal items)
/// with 2+ interleaved terminals. The first operand is the left operand
/// (handled by the Pratt loop), and subsequent operand-terminal pairs
/// become `MixfixPart`s.
///
/// Returns `(is_mixfix, parts)` where `parts` is empty for non-mixfix rules.
///
/// Example: `cond "?" then ":" else` → parts = [
///   MixfixPart { category: "Int", param: "then", following: Some(":") },
///   MixfixPart { category: "Int", param: "else", following: None },
/// ]
fn extract_mixfix_parts(syntax: &[SyntaxItemSpec]) -> (bool, Vec<MixfixPart>) {
    // Count operands (NonTerminal) and terminals
    let operand_count = syntax
        .iter()
        .filter(|item| matches!(item, SyntaxItemSpec::NonTerminal { .. }))
        .count();
    let terminal_count = syntax
        .iter()
        .filter(|item| matches!(item, SyntaxItemSpec::Terminal(_)))
        .count();

    // Mixfix: 3+ operands, 2+ terminals
    // (Regular infix: 2 operands, 1 terminal. Postfix: 1 operand, 1 terminal.)
    if operand_count < 3 || terminal_count < 2 {
        return (false, Vec::new());
    }

    // Extract parts: skip the first operand (left) and first terminal (trigger).
    // Remaining items alternate: NonTerminal, Terminal, NonTerminal, Terminal, ..., NonTerminal
    let mut parts = Vec::with_capacity(operand_count - 1);
    let mut after_trigger = false;
    let mut skip_count = 0;

    for item in syntax {
        match item {
            SyntaxItemSpec::NonTerminal { category: _, param_name: _ } if skip_count == 0 => {
                // First NonTerminal = left operand, skip it
                skip_count += 1;
            },
            SyntaxItemSpec::Terminal(_) if !after_trigger => {
                // First Terminal = trigger, skip it
                after_trigger = true;
            },
            SyntaxItemSpec::NonTerminal { category, param_name } if after_trigger => {
                parts.push(MixfixPart {
                    operand_category: category.clone(),
                    param_name: param_name.clone(),
                    following_terminal: None, // will be filled below
                });
            },
            SyntaxItemSpec::Terminal(t) if after_trigger => {
                // This terminal follows the previous part
                if let Some(last_part) = parts.last_mut() {
                    last_part.following_terminal = Some(t.clone());
                }
            },
            _ => {},
        }
    }

    (true, parts)
}

/// Convert a `SyntaxItemSpec` to an `RDSyntaxItem`.
///
/// Used for converting syntax items when building `RDRuleInfo` from `RuleSpec`.
fn convert_syntax_item_to_rd(item: &SyntaxItemSpec) -> RDSyntaxItem {
    match item {
        SyntaxItemSpec::Terminal(t) => RDSyntaxItem::Terminal(t.clone()),
        SyntaxItemSpec::NonTerminal { category, param_name } => RDSyntaxItem::NonTerminal {
            category: category.clone(),
            param_name: param_name.clone(),
        },
        SyntaxItemSpec::IdentCapture { param_name } => {
            RDSyntaxItem::IdentCapture { param_name: param_name.clone() }
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
        } => RDSyntaxItem::Collection {
            param_name: param_name.clone(),
            element_category: element_category.clone(),
            separator: separator.clone(),
            kind: *kind,
        },
        SyntaxItemSpec::ZipMapSep {
            left_name,
            right_name,
            left_category,
            right_category,
            body_items,
            separator,
        } => RDSyntaxItem::ZipMapSep {
            left_name: left_name.clone(),
            right_name: right_name.clone(),
            left_category: left_category.clone(),
            right_category: right_category.clone(),
            body_items: body_items.iter().map(convert_syntax_item_to_rd).collect(),
            separator: separator.clone(),
        },
        SyntaxItemSpec::Optional { inner } => RDSyntaxItem::Optional {
            inner: inner.iter().map(convert_syntax_item_to_rd).collect(),
        },
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// WFST static embedding (feature = "wfst")
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
#[cfg(feature = "wfst")]
fn emit_prediction_wfst_static(
    buf: &mut String,
    prediction_wfsts: &std::collections::BTreeMap<String, crate::wfst::PredictionWfst>,
) {
    use std::fmt::Write;

    for (category, wfst) in prediction_wfsts {
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
        write!(buf, "static WFST_TRANSITIONS_{cat}: &[(u16, u32, f64)] = &[", cat = category,)
            .unwrap();
        for (i, (token_id, target, weight)) in transitions_flat.iter().enumerate() {
            if i > 0 {
                buf.push(',');
            }
            write!(buf, "({}_u16, {}_u32, {:?}_f64)", token_id, target, weight).unwrap();
        }
        buf.push_str("];");

        // State offsets
        write!(
            buf,
            "static WFST_STATE_OFFSETS_{cat}: &[(usize, usize, bool, f64)] = &[",
            cat = category,
        )
        .unwrap();
        for (i, (start, count, is_final, fw)) in state_offsets.iter().enumerate() {
            if i > 0 {
                buf.push(',');
            }
            write!(buf, "({}_usize, {}_usize, {}, {:?}_f64)", start, count, is_final, fw).unwrap();
        }
        buf.push_str("];");

        // Token names
        write!(buf, "static WFST_TOKEN_NAMES_{cat}: &[&str] = &[", cat = category,).unwrap();
        for (i, name) in token_names.iter().enumerate() {
            if i > 0 {
                buf.push(',');
            }
            write!(buf, "\"{}\"", name).unwrap();
        }
        buf.push_str("];");

        // Beam width
        match wfst.beam_width {
            Some(bw) => write!(
                buf,
                "static WFST_BEAM_WIDTH_{}: Option<f64> = Some({:?}_f64);",
                category,
                bw.value(),
            )
            .unwrap(),
            None => {
                write!(buf, "static WFST_BEAM_WIDTH_{cat}: Option<f64> = None;", cat = category,)
                    .unwrap()
            },
        }

        // LazyLock constructor
        write!(buf,
            "static PREDICTION_{cat}: std::sync::LazyLock<mettail_prattail::wfst::PredictionWfst> = \
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
        ).unwrap();
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// WFST recovery static embedding (feature = "wfst")
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
#[cfg(feature = "wfst")]
fn emit_recovery_wfst_static(buf: &mut String, recovery_wfsts: &[crate::recovery::RecoveryWfst]) {
    use std::fmt::Write;

    for recovery_wfst in recovery_wfsts {
        let cat = recovery_wfst.category();

        // Sync token IDs (sorted)
        let sync_ids: Vec<u16> = recovery_wfst.sync_tokens().iter().copied().collect();
        write!(buf, "static RECOVERY_SYNC_TOKENS_{cat}: &[u16] = &[",).unwrap();
        for (i, id) in sync_ids.iter().enumerate() {
            if i > 0 {
                buf.push(',');
            }
            write!(buf, "{}_u16", id).unwrap();
        }
        buf.push_str("];");

        // Sync sources: (token_id, source_tag)
        // 0=Eof, 1=StructuralDelimiter, 2=FollowSet
        write!(buf, "static RECOVERY_SYNC_SOURCES_{cat}: &[(u16, u8)] = &[",).unwrap();
        for (i, &id) in sync_ids.iter().enumerate() {
            if i > 0 {
                buf.push(',');
            }
            let source_tag = match recovery_wfst.token_name(id) {
                Some("Eof") => 0_u8,
                Some("RParen" | "RBrace" | "RBracket" | "Semi" | "Comma") => 1_u8,
                _ => 2_u8,
            };
            write!(buf, "({}_u16, {}_u8)", id, source_tag).unwrap();
        }
        buf.push_str("];");

        // Token names for reconstructing TokenIdMap
        let mut token_names: Vec<String> = Vec::new();
        // Recover all token names from the sync set
        for &id in recovery_wfst.sync_tokens() {
            if let Some(name) = recovery_wfst.token_name(id) {
                token_names.push(name.to_string());
            }
        }
        token_names.sort();
        token_names.dedup();

        write!(buf, "static RECOVERY_TOKEN_NAMES_{cat}: &[&str] = &[",).unwrap();
        for (i, name) in token_names.iter().enumerate() {
            if i > 0 {
                buf.push(',');
            }
            write!(buf, "\"{}\"", name).unwrap();
        }
        buf.push_str("];");
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// WFST recovery codegen (feature = "wfst")
// ══════════════════════════════════════════════════════════════════════════════

/// Generate a WFST-based weighted recovery function for a category.
///
/// Emits a function `wfst_recover_Cat` that evaluates all 4 repair strategies
/// (skip-to-sync, delete, insert, substitute) with context-aware cost adjustments
/// from `RecoveryContext` (bracket balance, nesting depth, frame kind).
///
/// Also emits a helper `is_sync_token_Cat` for matching sync tokens.
///
/// Generated signatures:
/// ```text
/// fn wfst_recover_Cat<'a>(
///     tokens: &[(Token<'a>, Span)],
///     pos: &mut usize,
///     depth: usize,
///     binding_power: u8,
///     open_parens: u16,
///     open_braces: u16,
///     open_brackets: u16,
/// ) -> bool  // true if recovery succeeded
/// ```
#[cfg(feature = "wfst")]
fn generate_wfst_recovery_fn(
    buf: &mut String,
    category: &str,
    recovery_wfst: &crate::recovery::RecoveryWfst,
) {
    use std::fmt::Write;

    // Collect sync token variant names for match patterns
    let sync_patterns: Vec<String> = recovery_wfst
        .sync_tokens()
        .iter()
        .filter_map(|&id| recovery_wfst.token_name(id))
        .map(|name| match name {
            "Ident" => "Token::Ident(_)".to_string(),
            "Integer" => "Token::Integer(_)".to_string(),
            "Float" => "Token::Float(_)".to_string(),
            "Boolean" => "Token::Boolean(_)".to_string(),
            "StringLit" => "Token::StringLit(_)".to_string(),
            "Eof" => "Token::Eof".to_string(),
            other => format!("Token::{}", other),
        })
        .collect();

    if sync_patterns.is_empty() {
        return;
    }

    // Build bracket-specific insert patterns for close delimiters
    let has_rparen = recovery_wfst
        .sync_tokens()
        .iter()
        .any(|&id| recovery_wfst.token_name(id) == Some("RParen"));
    let has_rbrace = recovery_wfst
        .sync_tokens()
        .iter()
        .any(|&id| recovery_wfst.token_name(id) == Some("RBrace"));
    let has_rbracket = recovery_wfst
        .sync_tokens()
        .iter()
        .any(|&id| recovery_wfst.token_name(id) == Some("RBracket"));

    let max_skip: usize = 32; // Same as recovery::costs::MAX_SKIP_LOOKAHEAD

    // Generate the full 4-strategy context-aware recovery function
    write!(
        buf,
        "/// WFST-based 4-strategy context-aware recovery for category `{cat}`.
         ///
         /// Evaluates skip-to-sync, delete, insert, and substitute strategies with
         /// context-aware cost adjustments from nesting depth, binding power, and
         /// bracket balance.
         fn wfst_recover_{cat}<'a>(\
            tokens: &[(Token<'a>, Span)], \
            pos: &mut usize, \
            depth: usize, \
            binding_power: u8, \
            open_parens: u16, \
            open_braces: u16, \
            open_brackets: u16, \
         ) -> bool {{ \
            let start = *pos; \
            let remaining = tokens.len() - start; \
            let max_look = if remaining < {max_skip} {{ remaining }} else {{ {max_skip} }}; \
            let mut best_pos: Option<usize> = None; \
            let mut best_cost: f64 = f64::INFINITY; \
            /* Tier 1: depth-based skip multiplier */ \
            let skip_mult: f64 = if depth > 1000 {{ 0.5 }} \
                else if depth < 10 {{ 2.0 }} else {{ 1.0 }}; \
            /* Tier 1: BP-based skip multiplier */ \
            let bp_mult: f64 = if binding_power < 4 {{ 0.75 }} else {{ 1.0 }}; \
            let combined_skip_mult = skip_mult * bp_mult; \
            /* Strategy 1: Skip to nearest sync token (0.5/token * context mult) */ \
            for skip in 0..max_look {{ \
                let idx = start + skip; \
                if matches!(&tokens[idx].0, {sync_pats}) {{ \
                    let cost = (skip as f64) * 0.5 * combined_skip_mult; \
                    if cost < best_cost {{ \
                        best_cost = cost; \
                        best_pos = Some(idx); \
                    }} \
                    break; \
                }} \
            }} \
            /* Strategy 2: Delete one token (cost 1.0 * skip_mult) */ \
            if remaining > 0 {{ \
                let cost = 1.0 * combined_skip_mult; \
                if cost < best_cost {{ \
                    best_cost = cost; \
                    best_pos = Some(start + 1); \
                }} \
            }} \
            /* Strategy 3: Insert missing closing delimiter (bracket-aware) */ \
            {{ \
                let base_insert = 2.0_f64;",
        cat = category,
        max_skip = max_skip,
        sync_pats = sync_patterns.join(" | "),
    )
    .unwrap();

    // Emit bracket-specific insert logic
    if has_rparen {
        write!(
            buf,
            "if open_parens > 0 {{ \
                let cost = base_insert * 0.3; /* strongly prefer closing unmatched parens */ \
                if cost < best_cost {{ \
                    best_cost = cost; \
                    best_pos = Some(start); /* phantom insert — don't advance */ \
                }} \
            }}"
        )
        .unwrap();
    }
    if has_rbrace {
        write!(
            buf,
            "if open_braces > 0 {{ \
                let cost = base_insert * 0.3; \
                if cost < best_cost {{ \
                    best_cost = cost; \
                    best_pos = Some(start); \
                }} \
            }}"
        )
        .unwrap();
    }
    if has_rbracket {
        write!(
            buf,
            "if open_brackets > 0 {{ \
                let cost = base_insert * 0.3; \
                if cost < best_cost {{ \
                    best_cost = cost; \
                    best_pos = Some(start); \
                }} \
            }}"
        )
        .unwrap();
    }

    write!(
        buf,
        "   }} \
            /* Strategy 4: Substitute current token with sync token (cost 1.5 * sub_mult) */ \
            if remaining > 0 {{ \
                let sub_mult = 1.0_f64; /* mixfix/other adjustments could go here */ \
                let cost = 1.5 * sub_mult; \
                if cost < best_cost {{ \
                    best_cost = cost; \
                    best_pos = Some(start + 1); \
                }} \
            }} \
            /* Apply best strategy */ \
            match best_pos {{ \
                Some(new_pos) => {{ *pos = new_pos; true }} \
                None => false \
            }} \
         }}",
    )
    .unwrap();
}

/// Generate recovering parser variant that uses WFST recovery instead of sync_to.
///
/// On parse error, calls `wfst_recover_Cat()` with context parameters (depth,
/// binding power, bracket counters) for context-aware recovery with all 4 strategies.
///
/// Bracket counters are maintained inline: incremented on open delimiters,
/// decremented on close delimiters. This provides Tier 2 (bracket balance)
/// context to the recovery function at zero overhead on the happy path.
#[cfg(feature = "wfst")]
fn write_trampolined_parser_recovering_wfst(
    buf: &mut String,
    config: &crate::trampoline::TrampolineConfig,
) {
    use std::fmt::Write;

    let cat = &config.category;
    let parse_fn = if config.needs_dispatch {
        format!("parse_{}_own_recovering", cat)
    } else {
        format!("parse_{}_recovering", cat)
    };

    let own_parse_fn = if config.needs_dispatch {
        format!("parse_{}_own", cat)
    } else {
        format!("parse_{}", cat)
    };

    // Generate the recovering parser with bracket balance tracking.
    // The bracket counters are local to each recovering parse call.
    // For a truly integrated solution (Sprint 4+), these would be threaded
    // through the trampoline state. For now, we scan backwards from the
    // error position to estimate the current bracket balance.
    write!(
        buf,
        "fn {parse_fn}<'a>(\
            tokens: &[(Token<'a>, Span)], \
            pos: &mut usize, \
            min_bp: u8, \
            errors: &mut Vec<ParseError>, \
        ) -> Option<{cat}> {{ \
            match {own_parse_fn}(tokens, pos, min_bp) {{ \
                Ok(v) => Some(v), \
                Err(e) => {{ \
                    errors.push(e); \
                    /* Estimate bracket balance by scanning tokens consumed so far */ \
                    let mut op: u16 = 0; let mut ob: u16 = 0; let mut ok: u16 = 0; \
                    for i in 0..*pos {{ \
                        match &tokens[i].0 {{ \
                            Token::LParen => op = op.saturating_add(1), \
                            Token::RParen => op = op.saturating_sub(1), \
                            Token::LBrace => ob = ob.saturating_add(1), \
                            Token::RBrace => ob = ob.saturating_sub(1), \
                            Token::LBracket => ok = ok.saturating_add(1), \
                            Token::RBracket => ok = ok.saturating_sub(1), \
                            _ => {{}} \
                        }} \
                    }} \
                    wfst_recover_{cat}(tokens, pos, 0, min_bp, op, ob, ok); \
                    None \
                }} \
            }} \
        }}",
    )
    .unwrap();
}
