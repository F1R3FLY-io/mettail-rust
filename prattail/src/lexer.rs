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
        analyze_sparsity, generate_lexer_code, generate_lexer_string, terminal_to_variant_name,
        CodegenStrategy,
    },
    minimize::minimize_dfa,
    nfa::{build_nfa, BuiltinNeeds},
    partition::compute_equivalence_classes,
    subset::subset_construction,
    TerminalPattern, TokenKind,
};
use crate::LiteralPatterns;

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
}

/// Run the full lexer generation pipeline and return generated Rust code.
pub fn generate_lexer(input: &LexerInput) -> (TokenStream, LexerStats) {
    // Step 1: Build NFA from terminal patterns
    let nfa = build_nfa(&input.terminals, &input.needs, &input.literal_patterns);
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

    // Step 5: Analyze sparsity
    let sparsity = analyze_sparsity(&min_dfa);

    // Step 6: Generate code
    let (code, codegen_strategy) =
        generate_lexer_code(&min_dfa, &partition, &token_kinds, &input.language_name);

    let stats = LexerStats {
        num_terminals: input.terminals.len(),
        num_nfa_states,
        num_dfa_states,
        num_minimized_states,
        num_equiv_classes,
        codegen_strategy,
        dead_fraction: sparsity.dead_fraction,
    };

    (code, stats)
}

/// Run the full lexer generation pipeline and return generated Rust code as a string.
///
/// Same as `generate_lexer()` but returns a `String` instead of a `TokenStream`.
/// Used by `generate_parser()` to build a combined string buffer for a single
/// `parse::<TokenStream>()` call at the end, avoiding per-component proc_macro2 overhead.
pub fn generate_lexer_as_string(input: &LexerInput) -> (String, LexerStats) {
    // Step 1: Build NFA from terminal patterns
    let nfa = build_nfa(&input.terminals, &input.needs, &input.literal_patterns);
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

    // Step 5: Analyze sparsity
    let sparsity = analyze_sparsity(&min_dfa);

    // Step 6: Generate code as string
    let (code, codegen_strategy) =
        generate_lexer_string(&min_dfa, &partition, &token_kinds, &input.language_name);

    let stats = LexerStats {
        num_terminals: input.terminals.len(),
        num_nfa_states,
        num_dfa_states,
        num_minimized_states,
        num_equiv_classes,
        codegen_strategy,
        dead_fraction: sparsity.dead_fraction,
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
    // and the ZipMapSep handler checks for closing delimiters
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
