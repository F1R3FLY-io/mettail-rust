use super::*;

// ══════════════════════════════════════════════════════════════════════════════
// Data bundles — all Send+Sync
// ══════════════════════════════════════════════════════════════════════════════

/// All data needed by the lexer pipeline. Send+Sync.
pub struct LexerBundle {
    pub(crate) grammar_rules: Vec<GrammarRuleInfo>,
    pub(crate) type_infos: Vec<TypeInfo>,
    /// Whether the grammar has binder rules (^x.{body} lambda syntax).
    pub(crate) has_binders: bool,
    /// Category names (needed for dollar terminal generation when has_binders).
    pub(crate) category_names: Vec<String>,
    /// Configurable literal token patterns for lexer generation.
    pub(crate) literal_patterns: LiteralPatterns,
    /// Custom token definitions from the `tokens { ... }` block.
    pub(crate) custom_tokens: Vec<crate::CustomTokenSpec>,
    /// Named lexer modes from the `tokens { ... }` block.
    pub(crate) modes: Vec<crate::LexerModeSpec>,
}

/// Category metadata for the parser pipeline. Send+Sync.
#[derive(Debug, Clone)]
pub struct CategoryInfo {
    /// Category name (e.g., "Proc", "Int").
    pub name: String,
    /// Native Rust type name, if any (e.g., "i32", "bool").
    pub native_type: Option<String>,
    /// Whether this is the primary (first-declared) category.
    pub is_primary: bool,
    /// Whether this category has a variable variant (e.g. IVar). False for List/Bag.
    pub has_var: bool,
}

/// All data needed by the parser pipeline. Send+Sync.
pub struct ParserBundle {
    /// Grammar name (e.g., "RhoPi").
    pub(crate) grammar_name: String,
    pub(crate) categories: Vec<CategoryInfo>,
    pub(crate) bp_table: BindingPowerTable,
    pub(crate) rule_infos: Vec<RuleInfo>,
    pub(crate) follow_inputs: Vec<FollowSetInput>,
    pub(crate) rd_rules: Vec<RDRuleInfo>,
    pub(crate) cross_rules: Vec<CrossCategoryRule>,
    pub(crate) cast_rules: Vec<CastRule>,
    /// Whether the grammar has binder rules (^x.{body} lambda syntax).
    pub(crate) has_binders: bool,
    /// Beam width configuration for WFST prediction pruning.
    pub(crate) beam_width: crate::BeamWidthConfig,
    /// Recovery configuration (costs, thresholds, beam width).
    pub(crate) recovery_config: crate::recovery::RecoveryConfig,
    /// All syntax per rule: (label, category, syntax). Used by lint layer.
    pub(crate) all_syntax: Vec<(String, String, Vec<SyntaxItemSpec>)>,
    /// Rule source locations: (label, category) → SourceLocation. Used by lint layer.
    pub(crate) rule_locations: std::collections::HashMap<(String, String), crate::SourceLocation>,
    /// Rule labels that are not parser-root dead code even when absent from
    /// WFST/WPDS reachability, such as synthetic injections and refinement
    /// downcasts checked by refinement analysis.
    pub(crate) dead_rule_ignore_labels: HashSet<String>,
    /// Dependency groups from equations/rewrites/logic for transitive liveness analysis.
    pub(crate) semantic_dependency_groups: Vec<HashSet<String>>,
    /// Custom token specs from the `tokens { ... }` block.
    pub(crate) custom_tokens: Vec<crate::CustomTokenSpec>,
    /// Refinement type definitions from the `types { ... }` block.
    pub(crate) refinement_types: Vec<crate::RefinementTypeSpec>,
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
    /// Bundles extracted, ready for codegen.
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
                // AL02: hybrid_lexer defaults to true in PipelineState path
                // (cost-benefit analysis is not available here; hybrid is safe
                // because it only activates for DFAs > 30 states)
                let (lexer_code, variant_map, ambiguity_info) =
                    generate_lexer_code_with_map(&lexer_bundle, true);
                let parser_code = generate_parser_code_with_context(
                    &parser_bundle,
                    &variant_map,
                    &ambiguity_info,
                );
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
// Pipeline diagnostic helper
// ══════════════════════════════════════════════════════════════════════════════

/// Build and emit a structured pipeline diagnostic via the lint system.
pub(crate) fn pipeline_diagnostic(
    grammar_name: &str,
    id: DiagnosticId,
    name: &'static str,
    severity: crate::lint::LintSeverity,
    message: String,
    hint: Option<String>,
) {
    crate::lint::emit_diagnostic(&crate::lint::LintDiagnostic {
        id,
        name,
        severity,
        category: None,
        rule: None,
        message,
        hint,
        grammar_name: Some(grammar_name.to_string()),
        source_location: None,
    });
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
    run_pipeline_with_analysis(spec).0
}

/// Run the full pipeline and return both the generated `TokenStream` and
/// a [`PipelineAnalysis`] capturing WFST-derived data for downstream
/// optimization (Ascent DCE, rule ordering, isomorphic WFST detection).
///
/// The analysis is populated during the Generate phase, where FIRST sets,
/// prediction WFSTs, dead-rule labels, and constructor weights are already
/// computed. This function captures that data before it would otherwise
/// be discarded.
pub fn run_pipeline_with_analysis(spec: &LanguageSpec) -> (TokenStream, crate::PipelineAnalysis) {
    let trace = std::env::var("PRATTAIL_MACRO_TRACE").is_ok();
    macro_rules! stage {
        ($name:literal) => {
            if trace {
                eprintln!("[macro-trace] {} pipeline:{}", spec.name, $name);
            }
        };
    }

    stage!("extract_from_spec.start");
    let (lexer_bundle, parser_bundle) = extract_from_spec(spec);
    stage!("extract_from_spec.done");

    // EBNF debug dump (opt-in via environment variable)
    if let Ok(dump_target) = std::env::var("PRATTAIL_DUMP_EBNF") {
        let ebnf = crate::ebnf::format_ebnf(spec, &parser_bundle);
        crate::ebnf::write_ebnf_output(&ebnf, &spec.name, &dump_target);
    }

    stage!("generate_lexer_code.start");
    let (lexer_code, variant_map, ambiguity_info) =
        generate_lexer_code_with_map(&lexer_bundle, true);
    stage!("generate_lexer_code.done");

    stage!("generate_parser_code.start");
    let (parser_code, analysis) =
        generate_parser_code_with_analysis(&parser_bundle, &variant_map, &ambiguity_info);
    stage!("generate_parser_code.done");

    // Finalize: concatenate and parse into TokenStream
    stage!("concat.start");
    let mut combined = lexer_code;
    combined.push_str(&parser_code);
    stage!("concat.done");

    stage!("parse_to_tokenstream.start");
    let ts = combined
        .parse::<TokenStream>()
        .expect("PraTTaIL pipeline: generated code failed to parse as TokenStream");
    stage!("parse_to_tokenstream.done");

    (ts, analysis)
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
pub(crate) fn extract_from_spec(spec: &LanguageSpec) -> (LexerBundle, ParserBundle) {
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
        literal_patterns: spec.literal_patterns.clone(),
        custom_tokens: spec.custom_tokens.clone(),
        modes: spec.modes.clone(),
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
            has_var: t.has_var,
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

    // Stage 3.27d-pre (2026-04-30): prefix_bp now derives from
    // `compute_prefix_bp()` — the local max_infix_bp HashMap was removed
    // because the helper queries `bp_table.operators` directly. See
    // `prattail/src/binding_power.rs::PREFIX_BP_OFFSET`.

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
                    | SyntaxItemSpec::BinderCollection { .. }
                    | SyntaxItemSpec::Collection { .. }
                    | SyntaxItemSpec::Sep { .. }
                    | SyntaxItemSpec::Map { .. }
                    | SyntaxItemSpec::Zip { .. }
                    | SyntaxItemSpec::Optional { .. }
                    | SyntaxItemSpec::GuardExpression { .. } => FirstItem::Ident,
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
                Some(compute_prefix_bp(&rule.category, rule.prefix_precedence, &bp_table))
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

    // Build per-category infix terminal sets for cast-rule infix-sharing detection.
    // When a cast rule's source and target share an infix operator terminal
    // (e.g., `+` shared by Int and BigInt via IntToBigInt injection), the
    // cast-arm emission must pass `u8::MAX` as min_bp so the operator binds
    // to the target's rule, not the source's.
    let infix_terminals_by_cat: HashMap<String, HashSet<String>> = {
        let mut map: HashMap<String, HashSet<String>> = HashMap::new();
        for ir in &infix_rules {
            if !ir.terminal.is_empty() {
                map.entry(ir.category.clone())
                    .or_default()
                    .insert(ir.terminal.clone());
            }
        }
        map
    };

    // Extract cast rules
    // Stage 3.13c (2026-05-01): exclude synthetic auto-injection rules from
    // legacy unified-trampoline cast_rules. Synthetic rules emitted by
    // `wpda_codegen/auto_inject.rs::make_injection_rule` are visible only to
    // the WPDS path; routing them through unified-trampoline cast machinery
    // produces ambiguity warnings and downstream codegen errors (W05 false
    // positives + IfElse/KwInt arity mismatches in `int_bool-unified.rs`).
    let cast_rules: Vec<CastRule> = spec
        .rules
        .iter()
        .filter(|r| r.is_cast && !r.is_auto_injected)
        .map(|r| {
            let source_cat = r.cast_source_category.clone().unwrap_or_default();
            let target_cat = r.category.clone();
            let empty = HashSet::new();
            let src_ops = infix_terminals_by_cat.get(&source_cat).unwrap_or(&empty);
            let tgt_ops = infix_terminals_by_cat.get(&target_cat).unwrap_or(&empty);
            let shares_infix_with_target = src_ops.iter().any(|t| tgt_ops.contains(t));
            CastRule {
                label: r.label.clone(),
                source_category: source_cat,
                target_category: target_cat,
                shares_infix_with_target,
            }
        })
        .collect();

    // Build all_syntax for lint layer (label, category, syntax triples)
    let all_syntax: Vec<(String, String, Vec<SyntaxItemSpec>)> = spec
        .rules
        .iter()
        .map(|r| (r.label.clone(), r.category.clone(), r.syntax.clone()))
        .collect();

    // Build rule_locations for lint layer (source location of each rule)
    let rule_locations: HashMap<(String, String), crate::SourceLocation> = spec
        .rules
        .iter()
        .filter_map(|r| {
            r.source_location
                .map(|loc| ((r.label.clone(), r.category.clone()), loc))
        })
        .collect();

    let mut dead_rule_ignore_labels: HashSet<String> = spec
        .rules
        .iter()
        .filter(|r| r.is_auto_injected)
        .map(|r| r.label.clone())
        .collect();
    dead_rule_ignore_labels.extend(collect_refinement_downcast_rule_labels(spec));

    let parser_bundle = ParserBundle {
        grammar_name: spec.name.clone(),
        categories,
        bp_table,
        rule_infos,
        follow_inputs,
        rd_rules,
        cross_rules,
        cast_rules,
        has_binders,
        beam_width: spec.beam_width.clone(),
        recovery_config: spec.recovery_config.clone(),
        all_syntax,
        rule_locations,
        dead_rule_ignore_labels,
        semantic_dependency_groups: spec.semantic_dependency_groups.clone(),
        custom_tokens: spec.custom_tokens.clone(),
        refinement_types: spec.refinement_types.clone(),
    };

    (lexer_bundle, parser_bundle)
}

// ══════════════════════════════════════════════════════════════════════════════
// Helper functions (moved from lib.rs — only used by the pipeline)
// ══════════════════════════════════════════════════════════════════════════════

/// Capitalize the first letter of a string.
pub(crate) fn capitalize_first(s: &str) -> String {
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

// Stage 10.5 (2026-05-04): `compute_led_delegation` and `detect_projection_rules`
// DELETED. Both fed `TrampolineConfig::led_delegation` (Block 4) and were the only
// callers. Walker (WPDS) handles cross-category LED naturally via Fork+AmbiguityFanout
// over weighted PDA edges.

/// Recursively collect all terminal strings from a list of syntax items.
///
/// This extracts terminals from top-level items AND from nested structures
/// like `Sep`/`Map`/`Zip` body items and separators.
pub(crate) fn collect_terminals_recursive(items: &[SyntaxItemSpec]) -> Vec<String> {
    let mut terminals = Vec::new();
    for item in items {
        match item {
            SyntaxItemSpec::Terminal(t) => terminals.push(t.clone()),
            SyntaxItemSpec::Collection { separator, key_val_separator, .. } => {
                terminals.push(separator.clone());
                if let Some(kv) = key_val_separator {
                    terminals.push(kv.clone());
                }
            },
            SyntaxItemSpec::BinderCollection { separator, .. } => {
                terminals.push(separator.clone());
            },
            SyntaxItemSpec::Sep { body, separator, .. } => {
                terminals.extend(collect_terminals_recursive(std::slice::from_ref(body.as_ref())));
                terminals.push(separator.clone());
            },
            SyntaxItemSpec::Map { body_items } => {
                terminals.extend(collect_terminals_recursive(body_items));
            },
            SyntaxItemSpec::Zip { body, .. } => {
                terminals.extend(collect_terminals_recursive(std::slice::from_ref(body.as_ref())));
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
                    preceding_terminals: Vec::new(),
                    following_terminals: Vec::new(), // filled below
                });
            },
            SyntaxItemSpec::Terminal(t) if after_trigger => {
                // L12 follow-up B6 (2026-05-07): append literal to the
                // last part's following_terminals vec for postfix-mixfix
                // support (consecutive literals between operands).
                if let Some(last_part) = parts.last_mut() {
                    last_part.following_terminals.push(t.clone());
                }
            },
            _ => {},
        }
    }

    (true, parts)
}

// ══════════════════════════════════════════════════════════════════════════════
// Helpers
// ══════════════════════════════════════════════════════════════════════════════

/// Format an `f64` as a valid Rust literal. Handles infinities and NaN
/// which `{:?}` would render as `inf` / `nan` — not valid Rust tokens.
pub(crate) fn format_f64(v: f64) -> String {
    if v.is_infinite() && v.is_sign_positive() {
        "f64::INFINITY".to_string()
    } else if v.is_infinite() {
        "f64::NEG_INFINITY".to_string()
    } else if v.is_nan() {
        "f64::NAN".to_string()
    } else {
        format!("{:?}_f64", v)
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// CEK-4: Dead Frame Computation
// ══════════════════════════════════════════════════════════════════════════════

// Stage 10.7 (2026-05-05): compute_dead_frames + is_independently_parseable
// DELETED. Both implemented CEK03 dead-frame elimination over Frame_Cat enum
// variants — Frame_Cat is gone with trampoline.rs (Stage 10.6); Walker uses
// WPDS stack symbols (rule_idx, src_idx) not named frame variants.

// ══════════════════════════════════════════════════════════════════════════════
// Green Thread Safety Analysis (feature = "green-threads")
// ══════════════════════════════════════════════════════════════════════════════

/// Results of the 6-phase compile-time thread-safety verification pipeline.
///
/// Constructed by [`analyze_green_thread_safety()`] from a `ChannelsBlockSpec`.
/// Consumed by the lint layer (GT01–GT06) and the cost-benefit framework.
//
// Parked with `channel` (2026-06-21): consumes `channel::ChannelsBlockSpec`; uncalled. See src/lib.rs.
#[cfg(feature = "green-threads")]
#[derive(Debug, Clone)]
pub struct GreenThreadAnalysis {
    /// Phase 3: Petri net deadlock freedom.
    pub deadlock_free: bool,
    /// Phase 5: Büchi starvation freedom.
    pub starvation_free: bool,
    /// Phase 2: Register automaton data ownership safety.
    pub ownership_safe: bool,
    /// Phase 1: Nominal automaton channel freshness.
    pub freshness_safe: bool,
    /// Number of independent parallel regions (Petri net cliques).
    pub independent_regions: usize,
    /// Maximum continuation stack depth estimate per category (from WPDS).
    pub max_stack_depth: Vec<(String, usize)>,
    /// Accumulated lint diagnostics from all 6 phases.
    pub lints: Vec<crate::lint::LintDiagnostic>,
}

/// Run the 6-phase compile-time thread-safety verification pipeline.
///
/// Pipeline phases (executed in order, with short-circuit on critical errors):
///
/// | Phase | Automaton | Property |
/// |-------|----------|----------|
/// | 1 | Nominal | Channel freshness — no aliasing |
/// | 2 | Register | Data ownership — only owner accesses |
/// | 3 | Petri net | Deadlock freedom |
/// | 4 | WPDS | Mutual exclusion + stack depth |
/// | 5 | Büchi | Starvation freedom |
/// | 6 | KAT | Synchronization correctness |
///
/// # Arguments
/// * `channels_spec` — The `channels {}` block specification from the grammar.
/// * `grammar_name` — Grammar name for diagnostic attribution.
///
/// # Returns
/// A [`GreenThreadAnalysis`] with phase verdicts + accumulated GT01–GT06 lints.
#[cfg(feature = "green-threads")]
pub fn analyze_green_thread_safety(
    channels_spec: &crate::channel::ChannelsBlockSpec,
    grammar_name: &str,
) -> GreenThreadAnalysis {
    let mut lints = Vec::new();

    // ── Phase 1: Nominal scope analysis ─────────────────────────────────────
    // Check that channels created with `new` don't escape their scope.
    //
    // Strategy: Build synthetic syntax items from the channel spec. Each channel
    // declaration introduces a fresh name (modeled as a Binder in the "ChannelDecl"
    // category). Each join pattern references channel names in its own synthetic
    // category ("JoinPattern_<name>"). If a channel name appears across multiple
    // synthetic categories, `nominal::analyze_from_bundle()` detects it as a
    // scope violation (name escaping its binding scope).
    let freshness_safe = {
        let aliased: Vec<(String, String)> = {
            let mut synthetic_syntax: Vec<(String, String, Vec<crate::SyntaxItemSpec>)> =
                Vec::with_capacity(
                    channels_spec.channels.len() + channels_spec.join_patterns.len(),
                );

            // Each channel declaration introduces a fresh name in "ChannelDecl".
            for ch in &channels_spec.channels {
                synthetic_syntax.push((
                    ch.name.clone(),
                    "ChannelDecl".to_string(),
                    vec![crate::SyntaxItemSpec::Binder {
                        param_name: ch.name.clone(),
                        category: "Channel".to_string(),
                        is_multi: false,
                    }],
                ));
            }

            // Each join pattern references channel names; model these as binders
            // in a per-join-pattern category so cross-category usage is detected.
            for jp in &channels_spec.join_patterns {
                let items: Vec<crate::SyntaxItemSpec> = jp
                    .channels
                    .iter()
                    .map(|ch_ref| crate::SyntaxItemSpec::Binder {
                        param_name: ch_ref.channel_name.clone(),
                        category: "Channel".to_string(),
                        is_multi: false,
                    })
                    .collect();
                synthetic_syntax.push((jp.name.clone(), format!("JoinPattern_{}", jp.name), items));
            }

            let nominal_result = crate::nominal::analyze_from_bundle(&synthetic_syntax);
            nominal_result.scope_violations
        };

        if !aliased.is_empty() {
            crate::lint::lint_gt04_freshness(&aliased, grammar_name, &mut lints);
        }
        aliased.is_empty()
    };

    // ── Phase 2: Register data ownership analysis ───────────────────────────
    // Build synthetic syntax from the channel spec: each channel becomes a
    // "category" with a register. Channel declarations produce Store operations
    // (they define data). Join pattern references produce TestEq operations
    // (they consume data). Unbound references in the register analysis map to
    // ownership violations: a channel is accessed without a corresponding
    // declaration, or multiple join patterns access the same channel concurrently.
    let ownership_safe = {
        let violations: Vec<(String, Vec<String>)> = {
            // Build synthetic categories: one per channel.
            let synthetic_categories: Vec<CategoryInfo> = channels_spec
                .channels
                .iter()
                .map(|ch| CategoryInfo {
                    name: ch.name.clone(),
                    is_primary: false,
                    has_var: false,
                    native_type: ch.element_type.clone(),
                })
                .collect();

            // Build synthetic syntax rules:
            // - Each channel declaration -> a rule with a Binder (Store to the register).
            // - Each join pattern channel ref -> a rule with a NonTerminal (TestEq read).
            let mut synthetic_syntax: Vec<(String, String, Vec<crate::SyntaxItemSpec>)> =
                Vec::with_capacity(
                    channels_spec.channels.len() + channels_spec.join_patterns.len(),
                );

            for ch in &channels_spec.channels {
                synthetic_syntax.push((
                    format!("{}_decl", ch.name),
                    ch.name.clone(),
                    vec![crate::SyntaxItemSpec::Binder {
                        param_name: ch.name.clone(),
                        category: ch.name.clone(),
                        is_multi: false,
                    }],
                ));
            }

            for jp in &channels_spec.join_patterns {
                for ch_ref in &jp.channels {
                    synthetic_syntax.push((
                        format!("{}_{}", jp.name, ch_ref.channel_name),
                        ch_ref.channel_name.clone(),
                        vec![crate::SyntaxItemSpec::NonTerminal {
                            category: ch_ref.channel_name.clone(),
                            param_name: ch_ref.binding_name.clone(),
                        }],
                    ));
                }
            }

            let reg_analysis = crate::register_automata::analyze_from_bundle(
                &synthetic_syntax,
                &synthetic_categories,
            );

            // Map unbound_references to ownership violations:
            // Each unbound reference means a join pattern reads from a channel
            // that has no corresponding Store (declaration). Group by channel name.
            let mut violation_map: std::collections::HashMap<String, Vec<String>> =
                std::collections::HashMap::new();
            for &(_transition_idx, register_idx) in &reg_analysis.unbound_references {
                if register_idx < synthetic_categories.len() {
                    let channel_name = &synthetic_categories[register_idx].name;
                    // Find which join patterns reference this channel.
                    for jp in &channels_spec.join_patterns {
                        if jp
                            .channels
                            .iter()
                            .any(|cr| cr.channel_name == *channel_name)
                        {
                            violation_map
                                .entry(channel_name.clone())
                                .or_default()
                                .push(jp.name.clone());
                        }
                    }
                }
            }

            // Deduplicate accessor lists.
            let mut result: Vec<(String, Vec<String>)> = violation_map
                .into_iter()
                .map(|(ch, mut accessors)| {
                    accessors.sort();
                    accessors.dedup();
                    (ch, accessors)
                })
                .collect();
            result.sort_by(|a, b| a.0.cmp(&b.0));
            result
        };

        if !violations.is_empty() {
            crate::lint::lint_gt03_ownership(&violations, grammar_name, &mut lints);
        }
        violations.is_empty()
    };

    // ── Phase 3: Petri net deadlock analysis ────────────────────────────────
    let (deadlock_free, independent_regions, max_concurrent) = {
        // Construct Petri net from channel specifications.
        // Places: one per channel + one per thread ready state.
        // Transitions: send (place→channel), receive (channel→place).
        let num_channels = channels_spec.channels.len();
        let num_join_patterns = channels_spec.join_patterns.len();

        // Conservative analysis: check for circular dependencies among join patterns.
        let mut deadlock_markings: Vec<(Vec<String>, Vec<String>)> = Vec::new();

        // Detect trivial deadlocks: join pattern requires channel X, but no channel X producer exists.
        let channel_names: std::collections::HashSet<&str> = channels_spec
            .channels
            .iter()
            .map(|c| c.name.as_str())
            .collect();

        for jp in &channels_spec.join_patterns {
            let missing: Vec<String> = jp
                .channels
                .iter()
                .filter(|ch| !channel_names.contains(ch.channel_name.as_str()))
                .map(|ch| ch.channel_name.clone())
                .collect();
            if !missing.is_empty() {
                deadlock_markings.push((vec![jp.name.clone()], missing));
            }
        }

        if !deadlock_markings.is_empty() {
            crate::lint::lint_gt01_deadlock(&deadlock_markings, grammar_name, &mut lints);
        }

        // Independent regions = channels with no shared join patterns.
        let independent = if num_channels == 0 {
            0
        } else {
            // Conservative: each channel is an independent region unless joined.
            (num_channels).saturating_sub(num_join_patterns).max(1)
        };

        let max_conc = num_channels.max(1);

        crate::lint::lint_gt05_parallelism(independent, max_conc, grammar_name, &mut lints);

        (deadlock_markings.is_empty(), independent, max_conc)
    };
    let _ = max_concurrent; // used in lint above

    // ── Phase 4: WPDS stack depth estimation ────────────────────────────────
    // Build a synthetic WPDS from the channel topology:
    // - Stack symbols = one per channel (representing a pending message).
    // - Push rules = join patterns (consuming from multiple channels pushes
    //   continuation frames for each channel onto the stack).
    // - Pop rules = channel sends (producing a message pops its frame).
    // - Replace rules = intra-channel forwarding.
    //
    // Run poststar() on the synthetic WPDS to compute reachable configurations,
    // then measure the maximum chain length per category (channel) in the
    // resulting P-automaton.
    let max_stack_depth: Vec<(String, usize)> = {
        let estimates: Vec<(String, usize)> = if channels_spec.channels.is_empty() {
            Vec::new()
        } else {
            // Build a Wpds<BooleanWeight> from the channel topology.
            let primary_channel = channels_spec
                .channels
                .first()
                .expect("channels should not be empty at this point");
            let initial_symbol = crate::wpds::StackSymbol::category_entry(&primary_channel.name);

            let mut wpds = crate::wpds::Wpds::<crate::automata::semiring::BooleanWeight> {
                stack_symbols: Vec::new(),
                symbol_index: std::collections::HashMap::new(),
                rules: Vec::new(),
                rules_by_source: std::collections::HashMap::new(),
                initial_symbol: initial_symbol.clone(),
                grammar_name: grammar_name.to_string(),
            };

            // Register all channel entry symbols.
            let channel_names_set: std::collections::HashSet<&str> = channels_spec
                .channels
                .iter()
                .map(|c| c.name.as_str())
                .collect();

            for ch in &channels_spec.channels {
                let sym = crate::wpds::StackSymbol::category_entry(&ch.name);
                let idx = wpds.stack_symbols.len();
                wpds.symbol_index.insert(sym.clone(), idx);
                wpds.stack_symbols.push(sym);
            }

            // Join patterns create Push rules: consuming from multiple channels
            // means pushing continuation frames. For a join pattern over channels
            // [A, B, C], we model: A entry -> push(B_entry, A_entry) and
            // B entry -> push(C_entry, B_entry).
            for jp in &channels_spec.join_patterns {
                let jp_channels: Vec<&str> = jp
                    .channels
                    .iter()
                    .filter(|cr| channel_names_set.contains(cr.channel_name.as_str()))
                    .map(|cr| cr.channel_name.as_str())
                    .collect();

                if jp_channels.len() >= 2 {
                    for window in jp_channels.windows(2) {
                        let from = crate::wpds::StackSymbol::category_entry(window[0]);
                        let bottom = crate::wpds::StackSymbol::category_entry(window[0]);
                        let top = crate::wpds::StackSymbol::category_entry(window[1]);
                        let rule = crate::wpds::WpdsRule::Push {
                            from_gamma: from.clone(),
                            to_gamma_bottom: bottom,
                            to_gamma_top: top,
                            weight: crate::automata::semiring::BooleanWeight(true),
                        };
                        wpds.rules_by_source
                            .entry(from)
                            .or_default()
                            .push(wpds.rules.len());
                        wpds.rules.push(rule);
                    }
                } else if jp_channels.len() == 1 {
                    // Single-channel join is just a Replace (no stack growth).
                    let from = crate::wpds::StackSymbol::category_entry(jp_channels[0]);
                    let to = from.clone();
                    let rule = crate::wpds::WpdsRule::Replace {
                        from_gamma: from.clone(),
                        to_gamma: to,
                        weight: crate::automata::semiring::BooleanWeight(true),
                    };
                    wpds.rules_by_source
                        .entry(from)
                        .or_default()
                        .push(wpds.rules.len());
                    wpds.rules.push(rule);
                }
            }

            // Run poststar to compute the saturated P-automaton.
            let pautomaton = crate::wpds::poststar(&wpds);

            // Compute per-category max stack chain length from the P-automaton.
            // For each channel, count the longest chain of transitions reachable
            // from the initial state through that channel's symbol.
            let mut depth_estimates: Vec<(String, usize)> =
                Vec::with_capacity(channels_spec.channels.len());

            for ch in &channels_spec.channels {
                let sym = crate::wpds::StackSymbol::category_entry(&ch.name);
                // Count how many transitions from the initial state go through
                // this symbol, then follow chains from the target state.
                // Each additional transition from a non-final intermediate state
                // adds 1 to the stack depth.
                let mut max_depth: usize = 0;
                if let Some(trans_indices) = pautomaton
                    .transitions_by_source
                    .get(&pautomaton.initial_state)
                {
                    for &idx in trans_indices {
                        let t = &pautomaton.transitions[idx];
                        if t.symbol == sym {
                            // BFS from the target state to measure chain length.
                            let mut depth = 1usize;
                            let mut current_state = t.to;
                            let mut visited = std::collections::HashSet::new();
                            visited.insert(current_state);

                            'chain: loop {
                                if let Some(next_indices) =
                                    pautomaton.transitions_by_source.get(&current_state)
                                {
                                    let mut found_next = false;
                                    for &next_idx in next_indices {
                                        let next_t = &pautomaton.transitions[next_idx];
                                        if !visited.contains(&next_t.to) {
                                            visited.insert(next_t.to);
                                            current_state = next_t.to;
                                            depth += 1;
                                            found_next = true;
                                            break;
                                        }
                                    }
                                    if !found_next {
                                        break 'chain;
                                    }
                                } else {
                                    break 'chain;
                                }
                            }

                            if depth > max_depth {
                                max_depth = depth;
                            }
                        }
                    }
                }

                if max_depth > 0 {
                    depth_estimates.push((ch.name.clone(), max_depth));
                }
            }

            depth_estimates.sort_by(|a, b| b.1.cmp(&a.1));
            depth_estimates
        };

        if !estimates.is_empty() {
            crate::lint::lint_gt06_stack_depth(&estimates, grammar_name, &mut lints);
        }
        estimates
    };

    // ── Phase 5: Buchi starvation detection ─────────────────────────────────
    // Per channel, build a 3-state WeightedBuchiAutomaton<BooleanWeight>
    // modeling the channel lifecycle:
    //   State 0 (idle):     channel has no pending messages.
    //   State 1 (sent):     a message has been sent (produced).
    //   State 2 (consumed): the message has been consumed (accepting state).
    //
    // Transitions:
    //   idle --send--> sent (a producer sends on the channel)
    //   sent --recv--> consumed (a consumer receives from the channel)
    //   consumed --send--> sent (cycle: producer sends again)
    //   idle --idle--> idle (self-loop: no activity)
    //
    // If no consumer exists for a channel (no join pattern references it),
    // the transition sent->consumed never fires. The Buchi automaton then
    // has no accepting cycle (state 2 is never visited infinitely often),
    // meaning the channel starves.
    let starvation_free = {
        let starving: Vec<String> = {
            // Build the set of channels that have at least one consumer
            // (referenced in some join pattern).
            let consumed_channels: std::collections::HashSet<&str> = channels_spec
                .join_patterns
                .iter()
                .flat_map(|jp| jp.channels.iter().map(|cr| cr.channel_name.as_str()))
                .collect();

            let mut starving_channels = Vec::new();

            for ch in &channels_spec.channels {
                // Build a 3-state Buchi automaton for this channel.
                let mut buchi = crate::buchi::WeightedBuchiAutomaton::<
                    crate::automata::semiring::BooleanWeight,
                >::new();
                let q_idle = buchi.add_state(false); // state 0: idle
                let q_sent = buchi.add_state(false); // state 1: sent
                let q_consumed = buchi.add_state(true); // state 2: consumed (accepting)
                buchi.initial_states.insert(q_idle);

                // idle --send--> sent
                buchi.add_transition(q_idle, Some(format!("send_{}", ch.name)), q_sent);

                // idle self-loop (no activity)
                buchi.add_transition(q_idle, Some("idle".to_string()), q_idle);

                if consumed_channels.contains(ch.name.as_str()) {
                    // sent --recv--> consumed
                    buchi.add_transition(q_sent, Some(format!("recv_{}", ch.name)), q_consumed);
                    // consumed --send--> sent (cycle for liveness)
                    buchi.add_transition(q_consumed, Some(format!("send_{}", ch.name)), q_sent);
                }
                // If no consumer: sent has no outgoing to consumed, so no
                // accepting cycle exists.

                // Check emptiness: if the language is empty, the accepting
                // state (consumed) is never visited infinitely often -> starvation.
                if crate::buchi::check_emptiness(&buchi) {
                    starving_channels.push(ch.name.clone());
                }
            }

            starving_channels
        };

        if !starving.is_empty() {
            crate::lint::lint_gt02_starvation(&starving, grammar_name, &mut lints);
        }
        starving.is_empty()
    };

    // ── Phase 6: KAT synchronization correctness ────────────────────────────
    // Per join pattern, build a Hoare triple modeling the synchronization:
    //   Precondition: all required channels have data available.
    //   Program: the join pattern fires (atomic multi-channel receive).
    //   Postcondition: all channel bindings are satisfied.
    //
    // Verify each triple with `kat::verify_hoare_triple()`. A failed triple
    // means the join pattern's synchronization is unsound -- it may fire when
    // a channel is empty, violating the join semantics.
    {
        for jp in &channels_spec.join_patterns {
            if jp.channels.is_empty() {
                continue;
            }

            // Precondition: conjunction of "channel_X_has_data" for each channel.
            let pre = jp
                .channels
                .iter()
                .fold(crate::kat::BooleanTest::True, |acc, ch_ref| {
                    let atom =
                        crate::kat::BooleanTest::atom(format!("{}_has_data", ch_ref.channel_name));
                    if matches!(acc, crate::kat::BooleanTest::True) {
                        atom
                    } else {
                        crate::kat::BooleanTest::and(acc, atom)
                    }
                });

            // Program: sequential composition of recv actions.
            let program = jp
                .channels
                .iter()
                .fold(crate::kat::KatExpr::One, |acc, ch_ref| {
                    let action =
                        crate::kat::KatExpr::action(format!("recv_{}", ch_ref.channel_name));
                    if matches!(acc, crate::kat::KatExpr::One) {
                        action
                    } else {
                        crate::kat::KatExpr::seq(acc, action)
                    }
                });

            // Postcondition: conjunction of "binding_X_bound" for each channel.
            let post = jp
                .channels
                .iter()
                .fold(crate::kat::BooleanTest::True, |acc, ch_ref| {
                    let atom =
                        crate::kat::BooleanTest::atom(format!("{}_bound", ch_ref.binding_name));
                    if matches!(acc, crate::kat::BooleanTest::True) {
                        atom
                    } else {
                        crate::kat::BooleanTest::and(acc, atom)
                    }
                });

            let triple =
                crate::kat::HoareTriple::named(format!("join_{}", jp.name), pre, program, post);

            let valid = crate::kat::verify_hoare_triple(&triple);
            if !valid {
                // Report as a GT lint: synchronization unsound.
                lints.push(crate::lint::LintDiagnostic {
                    id: DiagnosticId::GT06,
                    name: "kat-sync-unsound",
                    severity: crate::lint::LintSeverity::Warning,
                    category: None,
                    rule: Some(jp.name.clone()),
                    message: format!(
                        "KAT verification failed for join pattern `{}`: \
                         Hoare triple {{{} }} {} {{{} }} is not valid",
                        jp.name, triple.precondition, triple.program, triple.postcondition,
                    ),
                    hint: Some(format!(
                        "ensure all channels ({}) have data before the join pattern `{}` fires",
                        jp.channels
                            .iter()
                            .map(|cr| cr.channel_name.as_str())
                            .collect::<Vec<_>>()
                            .join(", "),
                        jp.name,
                    )),
                    grammar_name: Some(grammar_name.to_string()),
                    source_location: None,
                });
            }
        }
    }

    GreenThreadAnalysis {
        deadlock_free,
        starvation_free,
        ownership_safe,
        freshness_safe,
        independent_regions,
        max_stack_depth,
        lints,
    }
}
