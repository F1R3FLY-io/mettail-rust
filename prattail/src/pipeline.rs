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
use crate::dispatch::{categories_needing_dispatch, write_category_dispatch, CastRule, CrossCategoryRule};
use crate::lexer::{extract_terminals, generate_lexer_as_string, GrammarRuleInfo, TypeInfo};
use crate::pratt::{
    write_dispatch_recovering, write_parser_helpers, write_pratt_parser,
    write_pratt_parser_recovering, write_recovery_helpers, PrattConfig, PrefixHandler,
};
use crate::prediction::{
    analyze_cross_category_overlaps, compute_first_sets, compute_follow_sets_from_inputs,
    detect_grammar_warnings, generate_sync_predicate, FirstItem, FollowSetInput, RuleInfo,
};
use crate::recursive::{write_dollar_handlers, write_lambda_handlers, write_rd_handler, RDRuleInfo, RDSyntaxItem};
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
}

// ══════════════════════════════════════════════════════════════════════════════
// Pipeline state machine
// ══════════════════════════════════════════════════════════════════════════════

/// Pipeline state machine for parallel code generation.
///
/// Each state holds the data needed for the next transition.
pub enum PipelineState {
    /// Bundles extracted, ready for parallel codegen.
    Ready {
        lexer_bundle: LexerBundle,
        parser_bundle: ParserBundle,
    },
    /// Both code strings generated, ready to merge.
    Generated {
        lexer_code: String,
        parser_code: String,
    },
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
            PipelineState::Ready {
                lexer_bundle,
                parser_bundle,
            } => {
                let lexer_code = generate_lexer_code(&lexer_bundle);
                let parser_code = generate_parser_code(&parser_bundle);
                PipelineState::Generated {
                    lexer_code,
                    parser_code,
                }
            }
            PipelineState::Generated {
                lexer_code,
                parser_code,
            } => {
                let mut combined = lexer_code;
                combined.push_str(&parser_code);
                let ts = combined
                    .parse::<TokenStream>()
                    .expect("PraTTaIL pipeline: generated code failed to parse as TokenStream");
                PipelineState::Complete(ts)
            }
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

    let mut state = PipelineState::Ready {
        lexer_bundle,
        parser_bundle,
    };
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

    let has_binders = spec.rules.iter().any(|r| r.has_binder || r.has_multi_binder);

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
                    }
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
                    }
                    "f32" | "f64" => {
                        first_set.insert("Float");
                    }
                    "bool" => {
                        first_set.insert("Boolean");
                    }
                    "str" | "String" => {
                        first_set.insert("StringLit");
                    }
                    _ => {}
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

    // Generate RD handlers
    let mut buf = String::with_capacity(8192);
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
    let dispatch_categories =
        categories_needing_dispatch(&bundle.cross_rules, &bundle.cast_rules);

    // Write parser helpers
    write_parser_helpers(&mut buf);

    // Write Pratt parsers per category
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

        let config = PrattConfig {
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
        };

        let cat_handlers: Vec<PrefixHandler> = all_prefix_handlers
            .iter()
            .filter(|h| h.category == cat.name)
            .cloned()
            .collect();

        write_pratt_parser(&mut buf, &config, &bundle.bp_table, &cat_handlers);
    }

    // Write cross-category dispatch
    for cat in &bundle.categories {
        let cat_cross: Vec<CrossCategoryRule> = bundle
            .cross_rules
            .iter()
            .filter(|r| r.result_category == cat.name)
            .cloned()
            .collect();
        if !cat_cross.is_empty() {
            write_category_dispatch(
                &mut buf,
                &cat.name,
                &cat_cross,
                &[],
                &overlaps,
                &first_sets,
            );
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

        let cat_cast_rules: Vec<CastRule> = bundle
            .cast_rules
            .iter()
            .filter(|r| r.target_category == cat.name)
            .cloned()
            .collect();

        let own_first = first_sets.get(&cat.name).cloned().unwrap_or_default();

        let config = PrattConfig {
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
            cast_rules: cat_cast_rules,
            own_first_set: own_first,
            all_first_sets: first_sets.clone(),
            follow_set: own_follow,
        };

        // Generate recovering Pratt parser
        write_pratt_parser_recovering(&mut buf, &config, &bundle.bp_table);

        // Generate recovering dispatch wrapper if needed
        if needs_dispatch {
            write_dispatch_recovering(&mut buf, &cat.name);
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
        }
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
            }
            SyntaxItemSpec::ZipMapSep {
                body_items,
                separator,
                ..
            } => {
                terminals.extend(collect_terminals_recursive(body_items));
                terminals.push(separator.clone());
            }
            SyntaxItemSpec::Optional { inner } => {
                terminals.extend(collect_terminals_recursive(inner));
            }
            _ => {}
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
            SyntaxItemSpec::NonTerminal {
                category: _,
                param_name: _,
            } if skip_count == 0 => {
                // First NonTerminal = left operand, skip it
                skip_count += 1;
            }
            SyntaxItemSpec::Terminal(_) if !after_trigger => {
                // First Terminal = trigger, skip it
                after_trigger = true;
            }
            SyntaxItemSpec::NonTerminal {
                category,
                param_name,
            } if after_trigger => {
                parts.push(MixfixPart {
                    operand_category: category.clone(),
                    param_name: param_name.clone(),
                    following_terminal: None, // will be filled below
                });
            }
            SyntaxItemSpec::Terminal(t) if after_trigger => {
                // This terminal follows the previous part
                if let Some(last_part) = parts.last_mut() {
                    last_part.following_terminal = Some(t.clone());
                }
            }
            _ => {}
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
        SyntaxItemSpec::NonTerminal {
            category,
            param_name,
        } => RDSyntaxItem::NonTerminal {
            category: category.clone(),
            param_name: param_name.clone(),
        },
        SyntaxItemSpec::IdentCapture { param_name } => RDSyntaxItem::IdentCapture {
            param_name: param_name.clone(),
        },
        SyntaxItemSpec::Binder {
            param_name,
            category,
        } => RDSyntaxItem::Binder {
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
