//! Lexer pipeline orchestration.
//!
//! Orchestrates the automata pipeline to generate a complete lexer:
//! 1. Extract terminal patterns from the language definition
//! 2. Build NFA via Thompson's construction
//! 3. Compute alphabet equivalence classes
//! 4. Convert NFA → DFA via subset construction
//! 5. Minimize DFA via Hopcroft's algorithm
//! 6. Generate Rust lexer code

use proc_macro2::TokenStream;

use crate::automata::{
    codegen::{
        analyze_sparsity, generate_lexer_code, generate_lexer_string,
        generate_lexer_string_hybrid, terminal_to_variant_name,
        CodegenStrategy, LexerAmbiguityInfo, TokenVariantMap,
    },
    minimize::minimize_dfa,
    nfa::{build_nfa_with_custom, BuiltinNeeds},
    partition::compute_equivalence_classes,
    subset::subset_construction,
    TerminalPattern, TokenKind,
};
use crate::{CustomTokenSpec, LiteralPatterns};

/// Information about a language's grammar needed for lexer generation.
pub struct LexerInput {
    /// Language name (for generated code comments/docs).
    pub language_name: String,
    /// All terminal patterns extracted from the grammar.
    pub terminals: Vec<TerminalPattern>,
    /// Which built-in patterns are needed.
    pub needs: BuiltinNeeds,
    /// Configurable literal token patterns for lexer generation.
    pub literal_patterns: LiteralPatterns,
    /// Custom token definitions from the `tokens { ... }` block.
    pub custom_tokens: Vec<CustomTokenSpec>,
    /// Named lexer modes (each gets its own NFA-to-DFA pipeline).
    pub modes: Vec<LexerModeInput>,
}

/// Input for a single named lexer mode's NFA-to-DFA pipeline.
#[derive(Debug, Clone)]
pub struct LexerModeInput {
    /// Mode name (e.g., "string_body").
    pub name: String,
    /// Custom token definitions within this mode.
    pub custom_tokens: Vec<CustomTokenSpec>,
}

/// Result of the NFA-to-DFA pipeline for a single named lexer mode.
#[derive(Debug, Clone)]
pub struct ModeDfaResult {
    /// Mode name.
    pub name: String,
    /// Mode index (0 = default, 1+ = named modes in declaration order).
    pub mode_id: u8,
    /// Minimized DFA for this mode.
    pub min_dfa: crate::automata::Dfa,
    /// Alphabet partition (equivalence classes) for this mode.
    pub partition: crate::automata::partition::AlphabetPartition,
    /// Token kinds in this mode.
    pub token_kinds: Vec<TokenKind>,
    /// Custom tokens in this mode (for codegen payload resolution).
    pub custom_tokens: Vec<CustomTokenSpec>,
}

/// Statistics from the lexer generation pipeline (for diagnostics).
#[derive(Debug, Clone)]
pub struct LexerStats {
    pub num_terminals: usize,
    pub num_nfa_states: usize,
    pub num_dfa_states: usize,
    pub num_minimized_states: usize,
    pub num_equiv_classes: usize,
    /// Which codegen strategy was selected for the transition table.
    pub codegen_strategy: CodegenStrategy,
    /// Fraction of DFA transitions that are DEAD (0.0 to 1.0).
    pub dead_fraction: f64,
    /// Bidirectional mapping between token variant names and compact u8 IDs.
    pub variant_map: TokenVariantMap,
    /// Information about ambiguous DFA states (multi-accept).
    pub ambiguity_info: LexerAmbiguityInfo,
}

/// Run the full lexer generation pipeline and return generated Rust code.
pub fn generate_lexer(input: &LexerInput) -> (TokenStream, LexerStats) {
    // Step 1: Build NFA from terminal patterns + custom tokens
    let nfa = build_nfa_with_custom(&input.terminals, &input.needs, &input.literal_patterns, &input.custom_tokens);
    let num_nfa_states = nfa.states.len();

    // Step 2: Compute alphabet equivalence classes
    let partition = compute_equivalence_classes(&nfa);
    let num_equiv_classes = partition.num_classes;

    // Step 3: Subset construction (NFA → DFA)
    let dfa = subset_construction(&nfa, &partition);
    let num_dfa_states = dfa.states.len();

    // Step 4: Minimize DFA
    let min_dfa = minimize_dfa(&dfa);
    let num_minimized_states = min_dfa.states.len();

    // Collect all token kinds for enum generation
    let mut token_kinds: Vec<TokenKind> = vec![TokenKind::Eof];
    if input.needs.ident {
        token_kinds.push(TokenKind::Ident);
    }
    if input.needs.integer {
        token_kinds.push(TokenKind::Integer);
    }
    if input.needs.float {
        token_kinds.push(TokenKind::Float);
    }
    if input.needs.boolean {
        token_kinds.push(TokenKind::True);
        token_kinds.push(TokenKind::False);
    }
    if input.needs.string_lit {
        token_kinds.push(TokenKind::StringLit);
    }
    for terminal in &input.terminals {
        token_kinds.push(terminal.kind.clone());
    }
    // Add custom (non-override) token kinds
    for spec in &input.custom_tokens {
        if !spec.is_builtin_override {
            token_kinds.push(TokenKind::Custom(spec.name.clone()));
        }
    }

    // Step 5: Analyze sparsity
    let sparsity = analyze_sparsity(&min_dfa);

    // Step 6: Generate code
    let (code, codegen_strategy) =
        generate_lexer_code(&min_dfa, &partition, &token_kinds, &input.language_name, &input.custom_tokens);

    // Build variant map and ambiguity info (also needed for diagnostics)
    let variant_map = TokenVariantMap::from_token_kinds(&token_kinds);
    let ambiguity_info = crate::automata::codegen::analyze_ambiguity(&min_dfa);

    let stats = LexerStats {
        num_terminals: input.terminals.len(),
        num_nfa_states,
        num_dfa_states,
        num_minimized_states,
        num_equiv_classes,
        codegen_strategy,
        dead_fraction: sparsity.dead_fraction,
        variant_map,
        ambiguity_info,
    };

    (code, stats)
}

/// Run the full lexer generation pipeline and return generated Rust code as a string.
///
/// Same as `generate_lexer()` but returns a `String` instead of a `TokenStream`.
/// Used by `generate_parser()` to build a combined string buffer for a single
/// `parse::<TokenStream>()` call at the end, avoiding per-component proc_macro2 overhead.
pub fn generate_lexer_as_string(input: &LexerInput) -> (String, LexerStats) {
    // Step 1: Build NFA from terminal patterns + custom tokens
    let nfa = build_nfa_with_custom(&input.terminals, &input.needs, &input.literal_patterns, &input.custom_tokens);
    let num_nfa_states = nfa.states.len();

    // Step 2: Compute alphabet equivalence classes
    let partition = compute_equivalence_classes(&nfa);
    let num_equiv_classes = partition.num_classes;

    // Step 3: Subset construction (NFA → DFA)
    let dfa = subset_construction(&nfa, &partition);
    let num_dfa_states = dfa.states.len();

    // Step 4: Minimize DFA
    let min_dfa = minimize_dfa(&dfa);
    let num_minimized_states = min_dfa.states.len();

    // Collect all token kinds for enum generation
    let mut token_kinds: Vec<TokenKind> = vec![TokenKind::Eof];
    if input.needs.ident {
        token_kinds.push(TokenKind::Ident);
    }
    if input.needs.integer {
        token_kinds.push(TokenKind::Integer);
    }
    if input.needs.float {
        token_kinds.push(TokenKind::Float);
    }
    if input.needs.boolean {
        token_kinds.push(TokenKind::True);
        token_kinds.push(TokenKind::False);
    }
    if input.needs.string_lit {
        token_kinds.push(TokenKind::StringLit);
    }
    for terminal in &input.terminals {
        token_kinds.push(terminal.kind.clone());
    }
    // Add custom (non-override) token kinds
    for spec in &input.custom_tokens {
        if !spec.is_builtin_override {
            token_kinds.push(TokenKind::Custom(spec.name.clone()));
        }
    }

    // Step 5: Analyze sparsity
    let sparsity = analyze_sparsity(&min_dfa);

    // Step 6: Generate code as string
    let (code, codegen_strategy, variant_map, ambiguity_info) =
        generate_lexer_string(&min_dfa, &partition, &token_kinds, &input.language_name, &input.custom_tokens);

    let stats = LexerStats {
        num_terminals: input.terminals.len(),
        num_nfa_states,
        num_dfa_states,
        num_minimized_states,
        num_equiv_classes,
        codegen_strategy,
        dead_fraction: sparsity.dead_fraction,
        variant_map,
        ambiguity_info,
    };

    (code, stats)
}

/// Run the full lexer generation pipeline with AL02 hybrid gating.
///
/// Same as [`generate_lexer_as_string`] but accepts the `hybrid_lexer` optimization gate.
/// When true and the DFA exceeds the direct-coded threshold, hot states (BFS depth ≤ 2)
/// are direct-coded while cold states use compressed table lookup.
pub fn generate_lexer_as_string_hybrid(input: &LexerInput, hybrid_lexer: bool) -> (String, LexerStats) {
    // Step 1: Build NFA from terminal patterns + custom tokens
    let nfa = build_nfa_with_custom(&input.terminals, &input.needs, &input.literal_patterns, &input.custom_tokens);
    let num_nfa_states = nfa.states.len();

    // Step 2: Compute alphabet equivalence classes
    let partition = compute_equivalence_classes(&nfa);
    let num_equiv_classes = partition.num_classes;

    // Step 3: Subset construction (NFA → DFA)
    let dfa = subset_construction(&nfa, &partition);
    let num_dfa_states = dfa.states.len();

    // Step 4: Minimize DFA
    let min_dfa = minimize_dfa(&dfa);
    let num_minimized_states = min_dfa.states.len();

    // Collect all token kinds for enum generation
    let mut token_kinds: Vec<TokenKind> = vec![TokenKind::Eof];
    if input.needs.ident {
        token_kinds.push(TokenKind::Ident);
    }
    if input.needs.integer {
        token_kinds.push(TokenKind::Integer);
    }
    if input.needs.float {
        token_kinds.push(TokenKind::Float);
    }
    if input.needs.boolean {
        token_kinds.push(TokenKind::True);
        token_kinds.push(TokenKind::False);
    }
    if input.needs.string_lit {
        token_kinds.push(TokenKind::StringLit);
    }
    for terminal in &input.terminals {
        token_kinds.push(terminal.kind.clone());
    }
    // Add custom (non-override) token kinds
    for spec in &input.custom_tokens {
        if !spec.is_builtin_override {
            token_kinds.push(TokenKind::Custom(spec.name.clone()));
        }
    }

    // Step 5: Analyze sparsity
    let sparsity = analyze_sparsity(&min_dfa);

    // Step 6: Generate code as string with hybrid gating
    let (mut code, codegen_strategy, variant_map, ambiguity_info) =
        generate_lexer_string_hybrid(&min_dfa, &partition, &token_kinds, &input.language_name, hybrid_lexer, &input.custom_tokens);

    // Step 7: If modes or stream annotations are present, use modal lexer codegen.
    // Stream-annotated tokens (-> stream_name) require the modal lex loop for routing
    // even if no explicit mode blocks are defined.
    let has_streams = input.custom_tokens.iter().any(|s| s.stream.is_some())
        || input.modes.iter().any(|m| m.custom_tokens.iter().any(|s| s.stream.is_some()));
    if !input.modes.is_empty() || has_streams {
        use crate::automata::nfa::build_nfa_for_mode;

        let mode_results: Vec<ModeDfaResult> = input.modes.iter().enumerate().map(|(i, mode_input)| {
            let mode_nfa = build_nfa_for_mode(&mode_input.custom_tokens);
            let mode_partition = compute_equivalence_classes(&mode_nfa);
            let mode_dfa = subset_construction(&mode_nfa, &mode_partition);
            let mode_min_dfa = minimize_dfa(&mode_dfa);

            let mode_token_kinds: Vec<TokenKind> = mode_input.custom_tokens.iter()
                .map(|spec| TokenKind::Custom(spec.name.clone()))
                .collect();

            ModeDfaResult {
                name: mode_input.name.clone(),
                mode_id: (i + 1) as u8,
                min_dfa: mode_min_dfa,
                partition: mode_partition,
                token_kinds: mode_token_kinds,
                custom_tokens: mode_input.custom_tokens.clone(),
            }
        }).collect();

        // Merge all mode token kinds into a combined list for the Token enum
        let mut all_custom_tokens = input.custom_tokens.clone();
        for mode in &input.modes {
            all_custom_tokens.extend(mode.custom_tokens.iter().cloned());
        }

        // Generate modal lexer code, replacing the single-DFA code
        code = crate::automata::codegen::generate_modal_lexer_string(
            &min_dfa,
            &partition,
            &token_kinds,
            &mode_results,
            &input.language_name,
            &input.custom_tokens,
            &all_custom_tokens,
        );
    }

    let stats = LexerStats {
        num_terminals: input.terminals.len(),
        num_nfa_states,
        num_dfa_states,
        num_minimized_states,
        num_equiv_classes,
        codegen_strategy,
        dead_fraction: sparsity.dead_fraction,
        variant_map,
        ambiguity_info,
    };

    (code, stats)
}

/// Extract terminal patterns and builtin needs from grammar rules.
///
/// Scans all grammar rules for terminal strings and determines which
/// built-in character-class patterns (identifier, integer, etc.) are needed.
pub fn extract_terminals(
    terms: &[GrammarRuleInfo],
    types: &[TypeInfo],
    has_binders: bool,
    category_names: &[String],
) -> LexerInput {
    let mut terminal_set = std::collections::BTreeSet::new();
    let mut needs = BuiltinNeeds {
        // Almost all grammars use identifiers for variables
        ident: true,
        ..Default::default()
    };

    // Always include structural delimiters — the Pratt parser uses ( ) for grouping
    // and the Sep handler checks for closing delimiters
    for text in &["(", ")", "{", "}", "[", "]", ","] {
        terminal_set.insert(TerminalPattern {
            text: text.to_string(),
            kind: TokenKind::Fixed(text.to_string()),
            is_keyword: false,
        });
    }

    // Add binder terminals (^ and .) for lambda syntax
    if has_binders {
        for text in &["^", "."] {
            terminal_set.insert(TerminalPattern {
                text: text.to_string(),
                kind: TokenKind::Fixed(text.to_string()),
                is_keyword: false,
            });
        }

        // Dollar terminals for function application syntax ($cat, $$cat()
        for cat_name in category_names {
            let cat_lower = cat_name.to_lowercase();
            // $cat (e.g., "$proc", "$name")
            let single = format!("${}", cat_lower);
            terminal_set.insert(TerminalPattern {
                text: single.clone(),
                kind: TokenKind::Fixed(single),
                is_keyword: false,
            });
            // $$cat( (e.g., "$$proc(", "$$name(")
            let multi = format!("$${}(", cat_lower);
            terminal_set.insert(TerminalPattern {
                text: multi.clone(),
                kind: TokenKind::Fixed(multi),
                is_keyword: false,
            });
        }
    }

    // Check for native types
    for ty in types {
        match ty.native_type_name.as_deref() {
            Some("i32") | Some("i64") | Some("u32") | Some("u64") | Some("isize")
            | Some("usize") => {
                needs.integer = true;
            },
            Some("f32") | Some("f64") => {
                needs.float = true;
            },
            Some("bool") => {
                needs.boolean = true;
                // Add "true" and "false" as keyword terminals
                terminal_set.insert(TerminalPattern {
                    text: "true".to_string(),
                    kind: TokenKind::True,
                    is_keyword: true,
                });
                terminal_set.insert(TerminalPattern {
                    text: "false".to_string(),
                    kind: TokenKind::False,
                    is_keyword: true,
                });
            },
            Some("str") | Some("String") => {
                needs.string_lit = true;
            },
            _ => {},
        }
    }

    // Extract terminals from grammar rules
    for rule in terms {
        for terminal in &rule.terminals {
            let text = terminal.clone();
            // Determine if this is a keyword (alphanumeric)
            let is_keyword = text.chars().all(|c| c.is_alphanumeric() || c == '_');
            terminal_set.insert(TerminalPattern {
                text: text.clone(),
                kind: TokenKind::Fixed(text),
                is_keyword,
            });
        }
    }

    let language_name = types
        .first()
        .map(|t| t.language_name.clone())
        .unwrap_or_else(|| "Unknown".to_string());

    LexerInput {
        language_name,
        terminals: terminal_set.into_iter().collect(),
        needs,
        literal_patterns: LiteralPatterns::default(),
        custom_tokens: Vec::new(),
        modes: Vec::new(),
    }
}

/// Simplified grammar rule information for terminal extraction.
/// This is a projection from the full GrammarRule AST type.
#[derive(Debug, Clone)]
pub struct GrammarRuleInfo {
    pub label: String,
    pub category: String,
    pub terminals: Vec<String>,
    pub is_infix: bool,
}

/// Simplified type information for lexer generation.
#[derive(Debug, Clone)]
pub struct TypeInfo {
    pub name: String,
    pub language_name: String,
    pub native_type_name: Option<String>,
}

/// Convert a terminal text to its Token variant name (re-export from codegen).
pub fn terminal_variant_name(text: &str) -> String {
    terminal_to_variant_name(text)
}

// Implement PartialEq, Eq, PartialOrd, Ord for TerminalPattern to allow BTreeSet
impl PartialOrd for TerminalPattern {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for TerminalPattern {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.text.cmp(&other.text)
    }
}
