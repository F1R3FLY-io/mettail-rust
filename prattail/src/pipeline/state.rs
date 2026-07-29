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
    /// Keyword-reservation policy (PIECE 3). Drives which identifier-shaped
    /// keyword terminals get their `Ident` co-accept dropped during subset
    /// construction. Default [`crate::ReservationMode::None`] → byte-identical.
    pub(crate) reservation_policy: crate::ReservationPolicy,
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

/// Pipeline state machine for code generation.
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
            // Forward-only state machine: Complete is terminal. Calling advance()
            // again is a caller contract violation (guard with is_complete() first).
            PipelineState::Complete(_) => {
                panic!("PraTTaIL pipeline: advance() called on the terminal Complete state — the pipeline state machine is forward-only and Complete is terminal; check is_complete() before advancing")
            },
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

/// Run the full pipeline: extract → generate → finalize.
///
/// This is the main entry point for code generation. It:
/// 1. Extracts Send+Sync bundles from `&LanguageSpec` on the current thread
/// 2. Runs lexer then parser codegen sequentially
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
    // Stage tracer gated by the `walker-trace` feature + `PRATTAIL_MACRO_TRACE`;
    // the env read compiles out on the default build (feature off ⇒ `trace` is a
    // constant `false` and every `stage!` body is dead-stripped). See
    // `crate::trace` module docs for why a `let` initializer uses this
    // `#[cfg]`/off-value idiom rather than `trace_diag!`.
    let trace = {
        #[cfg(feature = "walker-trace")]
        {
            std::env::var("PRATTAIL_MACRO_TRACE").is_ok()
        }
        #[cfg(not(feature = "walker-trace"))]
        {
            false
        }
    };
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

    // EBNF debug dump (opt-in via env var, behind the `walker-trace` feature).
    trace_diag! {
        if let Ok(dump_target) = std::env::var("PRATTAIL_DUMP_EBNF") {
            let ebnf = crate::ebnf::format_ebnf(spec, &parser_bundle);
            crate::ebnf::write_ebnf_output(&ebnf, &spec.name, &dump_target);
        }
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
        reservation_policy: spec.reservation_policy.clone(),
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
                shares_level_with_previous: r.shares_level_with_previous,
                is_cross_category: r.is_cross_category,
                is_postfix: r.is_postfix,
                is_mixfix,
                mixfix_parts,
                nullary_literals: Vec::new(),
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
                    | SyntaxItemSpec::TokenKindCapture { .. }
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
                    repetition: None,
                    // #131: this reconstruction serves the BINDING-POWER table only
                    // (precedence + associativity). A capture part yields no operand
                    // and therefore carries no binding power, so the bp view of a rule
                    // is the same whether or not a part is a capture — see
                    // `emit_mixfix_parts_fn` for the codegen view, which does
                    // distinguish them.
                    capture_kind: None,
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
