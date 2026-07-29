//! Lexer pipeline orchestration.
//!
//! Orchestrates the automata pipeline to generate a complete lexer:
//! 1. Extract terminal patterns from the language definition
//! 2. Build NFA via Thompson's construction
//! 3. Compute alphabet equivalence classes
//! 4. Convert NFA → DFA via subset construction
//! 5. Minimize DFA via Hopcroft's algorithm (skipped when both float and fixed-point literals are active)
//! 6. Generate Rust lexer code

use proc_macro2::TokenStream;

use crate::automata::{
    codegen::{
        analyze_sparsity, generate_lexer_code, generate_lexer_string, generate_lexer_string_hybrid,
        terminal_to_variant_name, CodegenStrategy, LexerAmbiguityInfo, TokenVariantMap,
    },
    minimize::minimize_dfa,
    nfa::{build_nfa_with_custom, BuiltinNeeds},
    partition::compute_equivalence_classes,
    subset::{subset_construction, subset_construction_with_reserved},
    ReservedKeywords, TerminalPattern, TokenKind,
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
    /// Reserved keyword token kinds (PIECE 3, keyword reservation). When a
    /// primary DFA accept is a reserved keyword, the generic `Ident`
    /// co-accept is dropped during subset construction. Empty by default →
    /// byte-identical lexer for languages that do not opt in.
    pub reserved_kinds: ReservedKeywords,
}

/// Input for a single named lexer mode's NFA-to-DFA pipeline.
#[derive(Debug, Clone)]
pub struct LexerModeInput {
    /// Mode name (e.g., "string_body").
    pub name: String,
    /// Custom token definitions within this mode.
    pub custom_tokens: Vec<CustomTokenSpec>,
    /// L9-4: RAW guest mode — no inter-token whitespace skip inside this mode.
    pub raw: bool,
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
    /// L9-4: RAW guest mode — the generated `m_is_raw(mode_id)` returns this so
    /// `compute_mode_map` / the modal DAG cores skip no whitespace inside it.
    pub raw: bool,
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
    let nfa = build_nfa_with_custom(
        &input.terminals,
        &input.needs,
        &input.literal_patterns,
        &input.custom_tokens,
    );
    let num_nfa_states = nfa.states.len();

    // Step 2: Compute alphabet equivalence classes
    let partition = compute_equivalence_classes(&nfa);
    let num_equiv_classes = partition.num_classes;

    // Step 3: Subset construction (NFA → DFA), applying keyword reservation.
    let dfa = subset_construction_with_reserved(&nfa, &partition, &input.reserved_kinds);
    let num_dfa_states = dfa.states.len();

    // Step 4: Minimize DFA. When both float and fixed-point literals are used, Hopcroft
    // minimization can merge states in ways that break maximal munch on shared prefixes
    // (e.g. `3.5` vs `3.5p0`). Use the subset DFA for the lexer in that case.
    let min_dfa = if input.needs.float && input.needs.fixed_point {
        dfa
    } else {
        minimize_dfa(&dfa)
    };
    let num_minimized_states = min_dfa.states.len();

    // Collect all token kinds for enum generation
    let mut token_kinds: Vec<TokenKind> = vec![TokenKind::Eof];
    if input.needs.ident {
        token_kinds.push(TokenKind::Ident);
    }
    if input.needs.integer {
        if input.literal_patterns.integer_by_category.is_empty() {
            token_kinds.push(TokenKind::Integer);
        } else {
            for cat in input.literal_patterns.integer_by_category.keys() {
                token_kinds.push(TokenKind::IntegerLit(cat.clone()));
            }
        }
    }
    if input.needs.float {
        token_kinds.push(TokenKind::Float);
    }
    if input.needs.boolean {
        if input.literal_patterns.boolean.is_some() {
            token_kinds.push(TokenKind::BooleanLit);
        } else {
            token_kinds.push(TokenKind::True);
            token_kinds.push(TokenKind::False);
        }
    }
    if input.needs.string_lit {
        token_kinds.push(TokenKind::StringLit);
    }
    if input.needs.rational {
        for cat in input.literal_patterns.rational_by_category.keys() {
            token_kinds.push(TokenKind::RationalLit(cat.clone()));
        }
    }
    if input.needs.fixed_point {
        for cat in input.literal_patterns.fixed_by_category.keys() {
            token_kinds.push(TokenKind::FixedPointLit(cat.clone()));
        }
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
    let (code, codegen_strategy) = generate_lexer_code(
        &min_dfa,
        &partition,
        &token_kinds,
        &input.language_name,
        &input.custom_tokens,
    );

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
    let nfa = build_nfa_with_custom(
        &input.terminals,
        &input.needs,
        &input.literal_patterns,
        &input.custom_tokens,
    );
    let num_nfa_states = nfa.states.len();

    // Step 2: Compute alphabet equivalence classes
    let partition = compute_equivalence_classes(&nfa);
    let num_equiv_classes = partition.num_classes;

    // Step 3: Subset construction (NFA → DFA), applying keyword reservation.
    let dfa = subset_construction_with_reserved(&nfa, &partition, &input.reserved_kinds);
    let num_dfa_states = dfa.states.len();

    // Step 4: Minimize DFA (see `generate_lexer` — skip minimization when float + fixed overlap).
    let min_dfa = if input.needs.float && input.needs.fixed_point {
        dfa
    } else {
        minimize_dfa(&dfa)
    };
    let num_minimized_states = min_dfa.states.len();

    // Collect all token kinds for enum generation
    let mut token_kinds: Vec<TokenKind> = vec![TokenKind::Eof];
    if input.needs.ident {
        token_kinds.push(TokenKind::Ident);
    }
    if input.needs.integer {
        if input.literal_patterns.integer_by_category.is_empty() {
            token_kinds.push(TokenKind::Integer);
        } else {
            for cat in input.literal_patterns.integer_by_category.keys() {
                token_kinds.push(TokenKind::IntegerLit(cat.clone()));
            }
        }
    }
    if input.needs.float {
        token_kinds.push(TokenKind::Float);
    }
    if input.needs.boolean {
        if input.literal_patterns.boolean.is_some() {
            token_kinds.push(TokenKind::BooleanLit);
        } else {
            token_kinds.push(TokenKind::True);
            token_kinds.push(TokenKind::False);
        }
    }
    if input.needs.string_lit {
        token_kinds.push(TokenKind::StringLit);
    }
    if input.needs.rational {
        for cat in input.literal_patterns.rational_by_category.keys() {
            token_kinds.push(TokenKind::RationalLit(cat.clone()));
        }
    }
    if input.needs.fixed_point {
        for cat in input.literal_patterns.fixed_by_category.keys() {
            token_kinds.push(TokenKind::FixedPointLit(cat.clone()));
        }
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
    let (code, codegen_strategy, variant_map, ambiguity_info) = generate_lexer_string(
        &min_dfa,
        &partition,
        &token_kinds,
        &input.language_name,
        &input.custom_tokens,
    );

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

// ⚠ `generate_lexer_as_string_hybrid` — the PANICKING WRAPPER — was DELETED here
// (#141 change 7, 2026-07-29). It read:
//
//     match try_generate_lexer_as_string_hybrid(input, hybrid_lexer) {
//         Ok(generated) => generated,
//         Err(rejection) => panic!("{}", rejection),
//     }
//
// and it, not the fallible form below, was what `pipeline::wfst_emit` called. The
// fallible form was reached only from this file's own tests.
//
// Its doc comment stated BOTH of the following, two sentences apart:
//
//   * "the current caller … runs inside the `#[proc_macro_error]` `language!`
//     expansion, WHERE A PANIC SURFACES AS A COMPILE ERROR";
//   * "a panic raised in this workspace's cranelift-compiled proc macro does not
//     unwind across the `proc_macro` bridge and ABORTS `rustc` WITH NO DIAGNOSTIC
//     AT ALL".
//
// The second is the measured one (`fatal runtime error: Rust cannot catch foreign
// exceptions` + `signal: 6, SIGABRT`). The first was false, and it is the sentence
// that justified the wrapper's existence. Both are gone with it: the rejection now
// travels as `Err(String)` from here to `macros/src/lib.rs`, which turns it into a
// `compile_error!` at the `language!` invocation.

/// Run the full lexer generation pipeline with AL02 hybrid gating, **returning** the
/// grammar-level rejection rather than raising it.
///
/// Same as [`generate_lexer_as_string`] but accepts the `hybrid_lexer` optimization gate.
/// When true and the DFA exceeds the direct-coded threshold, hot states (BFS depth ≤ 2)
/// are direct-coded while cold states use compressed table lookup.
///
/// # Errors
///
/// `Err(diagnostic)` iff the grammar fails one of the two modal soundness gates —
/// [`check_dui_soundness`] (a DFA state accepting tokens with *different* mode effects
/// at one position, which makes the active mode path-dependent) or
/// [`check_channel_soundness`] (co-accepts disagreeing on their token channel, which
/// makes the same span both trivia and a parse token). The diagnostic is the
/// user-facing message, and its destination is `compile_error!`: it is returned
/// up through [`crate::pipeline`] to `macros/src/lib.rs`, which is the only
/// frame that holds a span to attach it to.
pub fn try_generate_lexer_as_string_hybrid(
    input: &LexerInput,
    hybrid_lexer: bool,
) -> Result<(String, LexerStats), String> {
    // Stage tracer gated by the `walker-trace` feature + `PRATTAIL_MACRO_TRACE`;
    // the env read compiles out on the default build (feature off ⇒ `trace` is a
    // constant `false` and every `stage!` body — including its `$val` operands —
    // is dead-stripped, so the diagnostic-only stat bindings stay "used"). See
    // `crate::trace` module docs for the `let`-initializer off-value idiom.
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
        ($name:literal, $val:expr) => {
            if trace {
                eprintln!("[macro-trace] {} lexer:{} = {}", input.language_name, $name, $val);
            }
        };
        ($name:literal) => {
            if trace {
                eprintln!("[macro-trace] {} lexer:{}", input.language_name, $name);
            }
        };
    }

    stage!("build_nfa.start");
    let nfa = build_nfa_with_custom(
        &input.terminals,
        &input.needs,
        &input.literal_patterns,
        &input.custom_tokens,
    );
    let num_nfa_states = nfa.states.len();
    stage!("build_nfa.done", num_nfa_states);

    stage!("compute_equiv_classes.start");
    let partition = compute_equivalence_classes(&nfa);
    let num_equiv_classes = partition.num_classes;
    stage!("compute_equiv_classes.done", num_equiv_classes);

    stage!("subset_construction.start");
    let dfa = subset_construction_with_reserved(&nfa, &partition, &input.reserved_kinds);
    let num_dfa_states = dfa.states.len();
    stage!("subset_construction.done", num_dfa_states);

    stage!("minimize_dfa.start");
    let min_dfa = minimize_dfa(&dfa);
    let num_minimized_states = min_dfa.states.len();
    stage!("minimize_dfa.done", num_minimized_states);

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
    let (mut code, codegen_strategy, variant_map, ambiguity_info) = generate_lexer_string_hybrid(
        &min_dfa,
        &partition,
        &token_kinds,
        &input.language_name,
        hybrid_lexer,
        &input.custom_tokens,
    );

    // Step 7: If modes or stream annotations are present, use modal lexer codegen.
    // Stream-annotated tokens (-> stream_name) require the modal lex loop for routing
    // even if no explicit mode blocks are defined.
    let has_streams = input.custom_tokens.iter().any(|s| s.stream.is_some())
        || input
            .modes
            .iter()
            .any(|m| m.custom_tokens.iter().any(|s| s.stream.is_some()));
    if !input.modes.is_empty() || has_streams {
        use crate::automata::nfa::build_nfa_for_mode;

        let mode_results: Vec<ModeDfaResult> = input
            .modes
            .iter()
            .enumerate()
            .map(|(i, mode_input)| {
                let mode_nfa = build_nfa_for_mode(&mode_input.custom_tokens);
                let mode_partition = compute_equivalence_classes(&mode_nfa);
                let mode_dfa = subset_construction(&mode_nfa, &mode_partition);
                let mode_min_dfa = minimize_dfa(&mode_dfa);

                let mode_token_kinds: Vec<TokenKind> = mode_input
                    .custom_tokens
                    .iter()
                    .map(|spec| TokenKind::Custom(spec.name.clone()))
                    .collect();

                ModeDfaResult {
                    name: mode_input.name.clone(),
                    mode_id: (i + 1) as u8,
                    min_dfa: mode_min_dfa,
                    partition: mode_partition,
                    token_kinds: mode_token_kinds,
                    custom_tokens: mode_input.custom_tokens.clone(),
                    raw: mode_input.raw,
                }
            })
            .collect();

        // L9-2: Delimiter Unambiguity Invariant (DUI). Mode segmentation
        // (compute_mode_map) is sound ONLY if the active mode is a pure function
        // of byte position — i.e. every push/pop token is the unique
        // mode-changing accept at its position. Reject the grammar at COMPILE
        // time if any DFA state (default or a named mode) accepts a push/pop
        // token alongside a co-accept/alt-accept with a DIFFERENT mode effect,
        // which would make the post-position mode depend on the lattice path.
        // The check is a no-op for every non-modal grammar (no token carries a
        // push/pop effect, so no state can conflict). A violation is a hard
        // rejection, returned to the caller and propagated as `Err` all the way
        // to `macros/src/lib.rs`, which emits it as a `compile_error!` spanned at
        // the `language!` invocation.
        check_dui_soundness("default", &min_dfa, &input.custom_tokens)?;
        for mode_result in &mode_results {
            check_dui_soundness(
                &mode_result.name,
                &mode_result.min_dfa,
                &mode_result.custom_tokens,
            )?;
        }

        // Task #18: the analogous CHANNEL soundness check. A DFA state whose
        // co-accepts disagree on their token channel cannot be routed (the same
        // span would be both trivia and a parse token), so reject the grammar at
        // COMPILE time rather than silently picking one. A no-op for every
        // grammar with no `-> CHANNEL` annotation.
        check_channel_soundness("default", &min_dfa, &input.custom_tokens)?;
        for mode_result in &mode_results {
            check_channel_soundness(
                &mode_result.name,
                &mode_result.min_dfa,
                &mode_result.custom_tokens,
            )?;
        }

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

    Ok((code, stats))
}

/// The lexer-mode effect a token's accept carries (L9-2 DUI analysis).
#[derive(Debug, Clone, PartialEq, Eq)]
enum ModeEffect {
    /// Ordinary token — no mode change.
    None,
    /// Push the named mode after accepting.
    Push(String),
    /// Pop the current mode after accepting.
    Pop,
}

/// Resolve a token kind's mode effect against a mode's custom-token specs.
/// Only `Custom` tokens can carry push/pop; everything else is `None`.
fn token_mode_effect(kind: &TokenKind, custom_tokens: &[CustomTokenSpec]) -> ModeEffect {
    if let TokenKind::Custom(name) = kind {
        if let Some(spec) = custom_tokens.iter().find(|s| s.name == *name) {
            if let Some(target) = &spec.push_mode {
                return ModeEffect::Push(target.clone());
            }
            if spec.is_pop {
                return ModeEffect::Pop;
            }
        }
    }
    ModeEffect::None
}

/// Resolve the token CHANNEL a kind routes to (task #18): `None` = `DEFAULT`
/// (the parse stream), `Some(name)` = the alternative channel its `-> CHANNEL`
/// annotation declares. Only `Custom` tokens can carry a channel; a built-in
/// kind is always `DEFAULT`. `-> main` is spelled out as `DEFAULT` so the two
/// spellings of the parse stream compare equal.
fn token_channel<'a>(
    kind: &TokenKind,
    custom_tokens: &'a [CustomTokenSpec],
) -> Option<&'a str> {
    if let TokenKind::Custom(name) = kind {
        if let Some(spec) = custom_tokens.iter().find(|s| s.name == *name) {
            return spec.stream.as_deref().filter(|stream| *stream != "main");
        }
    }
    None
}

/// Task #18: enforce CHANNEL soundness for ONE mode's DFA.
///
/// A token routed to an alternative channel is TRIVIA — the scanner consumes its
/// span and delivers nothing to the parser. The routing decision is made per
/// ACCEPTING STATE (`stream_id_*`), so every co-accepting kind at a state must
/// agree on its channel. A state that accepts a channel-routed token alongside a
/// `DEFAULT` one (or alongside a token on a DIFFERENT channel) is a grammar the
/// mechanism cannot express: the identical span would have to be simultaneously
/// discarded-as-trivia and delivered-as-a-token, and which happened would depend
/// on which accept the scanner happened to consult.
///
/// This is the exact analogue of [`check_dui_soundness`] for channels, and it
/// fails CLOSED at compile time for the same reason: silently picking one is a
/// latent, position-dependent bug. Ordinary intra-channel ambiguity (all
/// co-accepts on the same channel — including the overwhelmingly common
/// all-`DEFAULT` case) is sound and accepted, so the check is a no-op for every
/// grammar with no `-> CHANNEL` annotation.
///
/// Returns `Err(diagnostic)` describing the first violating state, else `Ok(())`.
fn check_channel_soundness(
    mode_label: &str,
    dfa: &crate::automata::Dfa,
    custom_tokens: &[CustomTokenSpec],
) -> Result<(), String> {
    for (state_idx, state) in dfa.states.iter().enumerate() {
        // Gather the DISTINCT accepting kinds at this state — same union as
        // `check_dui_soundness` (`alt_accepts` already includes the primary
        // winner when non-empty, so union with `accept` and dedupe).
        let mut kinds: Vec<TokenKind> = Vec::new();
        if let Some(k) = &state.accept {
            if !kinds.contains(k) {
                kinds.push(k.clone());
            }
        }
        for (k, _w) in &state.alt_accepts {
            if !kinds.contains(k) {
                kinds.push(k.clone());
            }
        }
        if kinds.len() < 2 {
            continue; // a single accepting kind cannot conflict with itself
        }

        let mut distinct: Vec<Option<&str>> = Vec::new();
        for k in &kinds {
            let channel = token_channel(k, custom_tokens);
            if !distinct.contains(&channel) {
                distinct.push(channel);
            }
        }
        if distinct.len() < 2 {
            continue; // every co-accept agrees on its channel
        }

        let mut parts: Vec<String> = Vec::with_capacity(kinds.len());
        for k in &kinds {
            let name = match k {
                TokenKind::Custom(n) => n.clone(),
                TokenKind::Ident => "<identifier>".to_string(),
                TokenKind::Fixed(t) => format!("\"{}\"", t),
                other => format!("{:?}", other),
            };
            let channel = match token_channel(k, custom_tokens) {
                Some(stream) => format!("-> {}", stream),
                None => "DEFAULT".to_string(),
            };
            parts.push(format!("`{}` [{}]", name, channel));
        }
        return Err(format!(
            "channel violation in mode `{}`: DFA state {} accepts {} at the SAME position on \
             DIFFERENT token channels. A channel-routed token is TRIVIA — its span is consumed \
             and never delivered to the parser — so one span cannot be both trivia and a parse \
             token. Hint: make the channel-routed pattern strictly distinguishable (e.g. a longer \
             or disjoint delimiter) so maximal munch selects a unique channel at this position.",
            mode_label,
            state_idx,
            parts.join(" vs "),
        ));
    }
    Ok(())
}

/// L9-2: enforce the Delimiter Unambiguity Invariant for ONE mode's DFA.
///
/// For every accepting state, the set of accepting token kinds must induce a
/// SINGLE mode effect whenever any of them is a push/pop token. A state that
/// accepts a push/pop token alongside a co-accept / alt-accept with a DIFFERENT
/// effect makes the post-position mode depend on which lattice path the parser
/// follows — [`compute_mode_map`](crate::runtime_types::compute_mode_map) would
/// no longer be a pure function of position. Ordinary intra-mode ambiguity (all
/// co-accepts carry the SAME effect, e.g. two closers that both pop, or the
/// classic `-` / integer overlap where neither changes mode) is sound and
/// accepted.
///
/// Returns `Err(diagnostic)` describing the first violating state, else `Ok(())`.
/// The diagnostic tailors its remediation hint to whether one of the colliding
/// kinds is a bare identifier (a keyword-reservation problem) or a longer
/// distinguishing delimiter is needed.
fn check_dui_soundness(
    mode_label: &str,
    dfa: &crate::automata::Dfa,
    custom_tokens: &[CustomTokenSpec],
) -> Result<(), String> {
    for (state_idx, state) in dfa.states.iter().enumerate() {
        // Gather the DISTINCT accepting kinds at this state. `alt_accepts`
        // already includes the primary winner when non-empty; union with
        // `accept` and dedupe so a lone accept (empty `alt_accepts`) is covered.
        let mut kinds: Vec<TokenKind> = Vec::new();
        if let Some(k) = &state.accept {
            if !kinds.contains(k) {
                kinds.push(k.clone());
            }
        }
        for (k, _w) in &state.alt_accepts {
            if !kinds.contains(k) {
                kinds.push(k.clone());
            }
        }
        if kinds.len() < 2 {
            continue; // a single accepting kind cannot conflict with itself
        }

        // Distinct mode effects among the co-accepts.
        let mut distinct: Vec<ModeEffect> = Vec::new();
        for k in &kinds {
            let effect = token_mode_effect(k, custom_tokens);
            if !distinct.contains(&effect) {
                distinct.push(effect);
            }
        }
        let has_push_pop = distinct.iter().any(|e| *e != ModeEffect::None);
        if !has_push_pop || distinct.len() < 2 {
            // All-`None` (ordinary intra-mode ambiguity) or a single shared
            // effect (e.g. two closers popping the same way) is sound.
            continue;
        }

        // Violation — describe every conflicting token and its effect.
        let mut parts: Vec<String> = Vec::with_capacity(kinds.len());
        for k in &kinds {
            let name = match k {
                TokenKind::Custom(n) => n.clone(),
                TokenKind::Ident => "<identifier>".to_string(),
                TokenKind::Fixed(t) => format!("\"{}\"", t),
                other => format!("{:?}", other),
            };
            let effect = match token_mode_effect(k, custom_tokens) {
                ModeEffect::Push(m) => format!("push({})", m),
                ModeEffect::Pop => "pop".to_string(),
                ModeEffect::None => "no mode change".to_string(),
            };
            parts.push(format!("`{}` [{}]", name, effect));
        }
        let mentions_ident = kinds.iter().any(|k| matches!(k, TokenKind::Ident));
        let hint = if mentions_ident {
            " Hint: a mode-changing delimiter must not also lex as a bare identifier — \
             reserve it as a keyword or give it a distinguishing delimiter so maximal \
             munch selects a unique token at this position."
        } else {
            " Hint: make the mode-changing delimiter strictly longer than the colliding \
             token (e.g. a reserved-keyword tag) so maximal munch selects a unique \
             mode-changing token at this position."
        };
        return Err(format!(
            "DUI violation in mode `{}`: DFA state {} accepts {} at the SAME position with \
             DIFFERENT mode effects. Multi-mode lexing requires the active mode to be a pure \
             function of byte position; a position where one alternative pushes/pops a mode \
             and another does not (or pushes a different mode) makes the mode path-dependent \
             and unsound.{}",
            mode_label,
            state_idx,
            parts.join(" vs "),
            hint,
        ));
    }
    Ok(())
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
            Some("i8") | Some("i16") | Some("i32") | Some("i64") | Some("i128") | Some("u8")
            | Some("u16") | Some("u32") | Some("u64") | Some("u128") | Some("isize")
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
            Some(other)
                // BigInt (incl. CanonicalBigInt) needs integer tokenization. BigRat / CanonicalBigRat
                // uses the separate rational literal path when configured in `literals { ... }`;
                // constructor-only languages should not pull in the legacy `...r` integer suffix.
                if other.ends_with("BigInt") =>
            {
                needs.integer = true;
            },
            Some(other) if other.ends_with("CanonicalFixedPoint") => {
                needs.fixed_point = true;
            },
            Some(_) => {},
            None => {},
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
        // Populated by the caller (`generate_lexer_code_with_map`) from the
        // language's reservation policy; empty here → no reservation.
        reserved_kinds: ReservedKeywords::none(),
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

#[cfg(test)]
mod dui_tests {
    use super::*;
    use crate::automata::semiring::TropicalWeight;
    use crate::automata::{Dfa, DfaState};

    /// Build a `CustomTokenSpec` with the given name/pattern and mode effect.
    fn dui_spec(name: &str, pattern: &str, push: Option<&str>, pop: bool) -> CustomTokenSpec {
        CustomTokenSpec {
            name: name.to_string(),
            pattern: pattern.to_string(),
            category: None,
            payload_type: None,
            constructor_code: None,
            is_builtin_override: false,
            priority: 2,
            push_mode: push.map(|s| s.to_string()),
            is_pop: pop,
            stream: None,
        }
    }

    /// A two-state DFA whose state 1 accepts `primary` plus the given alternates.
    fn dfa_with_accepts(primary: TokenKind, alts: Vec<TokenKind>) -> Dfa {
        let mut accepting = DfaState::with_classes(1);
        accepting.accept = Some(primary.clone());
        if !alts.is_empty() {
            // `alt_accepts` includes the primary winner (per DfaState docs).
            accepting.alt_accepts.push((primary, TropicalWeight::new(1.0)));
            for (i, a) in alts.into_iter().enumerate() {
                accepting.alt_accepts.push((a, TropicalWeight::new(2.0 + i as f64)));
            }
        }
        Dfa { states: vec![DfaState::with_classes(1), accepting], start: 0, num_classes: 1 }
    }

    fn build_default_dfa(custom_tokens: &[CustomTokenSpec], needs: BuiltinNeeds) -> Dfa {
        let lp = LiteralPatterns::default();
        let terminals: Vec<TerminalPattern> = Vec::new();
        let nfa = build_nfa_with_custom(&terminals, &needs, &lp, custom_tokens);
        let partition = compute_equivalence_classes(&nfa);
        let dfa = subset_construction(&nfa, &partition);
        minimize_dfa(&dfa)
    }

    #[test]
    fn dui_single_push_accept_ok() {
        let dfa = dfa_with_accepts(TokenKind::Custom("FltOpenBacktick".into()), vec![]);
        let specs = vec![dui_spec("FltOpenBacktick", "x`", Some("guest"), false)];
        assert!(check_dui_soundness("default", &dfa, &specs).is_ok());
    }

    #[test]
    fn dui_plain_multilength_ambiguity_ok() {
        // `-`/integer overlap: two co-accepts, NEITHER changes mode → sound.
        let dfa = dfa_with_accepts(
            TokenKind::Integer,
            vec![TokenKind::Fixed("-".into()), TokenKind::Integer],
        );
        assert!(check_dui_soundness("default", &dfa, &[]).is_ok());
    }

    #[test]
    fn dui_two_closers_same_pop_ok() {
        // Two closers that both pop induce a SINGLE effect (Pop) → sound.
        let dfa = dfa_with_accepts(
            TokenKind::Custom("CloseA".into()),
            vec![TokenKind::Custom("CloseB".into())],
        );
        let specs = vec![
            dui_spec("CloseA", "`", None, true),
            dui_spec("CloseB", "`", None, true),
        ];
        assert!(check_dui_soundness("m", &dfa, &specs).is_ok());
    }

    #[test]
    fn dui_push_vs_plain_rejected() {
        let dfa = dfa_with_accepts(
            TokenKind::Custom("PushBang".into()),
            vec![TokenKind::Custom("PlainBang".into())],
        );
        let specs = vec![
            dui_spec("PushBang", "!", Some("inner"), false),
            dui_spec("PlainBang", "!", None, false),
        ];
        let err = check_dui_soundness("default", &dfa, &specs).expect_err("must reject");
        assert!(err.contains("DUI violation"), "clear diagnostic: {err}");
        assert!(err.contains("PushBang") && err.contains("PlainBang"));
    }

    #[test]
    fn dui_conflicting_push_targets_rejected() {
        let dfa = dfa_with_accepts(
            TokenKind::Custom("OpenA".into()),
            vec![TokenKind::Custom("OpenB".into())],
        );
        let specs = vec![
            dui_spec("OpenA", "@", Some("modeA"), false),
            dui_spec("OpenB", "@", Some("modeB"), false),
        ];
        let err = check_dui_soundness("default", &dfa, &specs).expect_err("must reject");
        assert!(err.contains("push(modeA)") && err.contains("push(modeB)"));
    }

    #[test]
    fn dui_push_vs_ident_rejected_with_keyword_hint() {
        // A push token that ALSO lexes as a bare identifier → keyword-reservation
        // flavored diagnostic.
        let dfa = dfa_with_accepts(
            TokenKind::Custom("BareOpener".into()),
            vec![TokenKind::Ident],
        );
        let specs = vec![dui_spec("BareOpener", "[a-z]+", Some("guest"), false)];
        let err = check_dui_soundness("default", &dfa, &specs).expect_err("must reject");
        assert!(err.contains("reserve it as a keyword"), "keyword hint: {err}");
    }

    #[test]
    fn dui_real_pipeline_same_pattern_conflict_rejected() {
        // Real NFA→DFA pipeline: two tokens sharing the pattern "!" with
        // different mode effects collapse to one accepting state → rejected.
        let specs = vec![
            dui_spec("PushBang", "!", Some("inner"), false),
            dui_spec("PlainBang", "!", None, false),
        ];
        let dfa = build_default_dfa(&specs, BuiltinNeeds::default());
        let res = check_dui_soundness("default", &dfa, &specs);
        assert!(res.is_err(), "real-DFA same-pattern conflict must be rejected: {res:?}");
    }

    #[test]
    fn dui_real_pipeline_backtick_opener_ok() {
        // FltOpenBacktick = "[a-z]+`" is longer than the built-in Ident, so the
        // opener accepts at its OWN post-backtick state — no same-state conflict.
        let needs = BuiltinNeeds { ident: true, ..Default::default() };
        let specs = vec![dui_spec("FltOpenBacktick", "[a-z]+`", Some("guest"), false)];
        let dfa = build_default_dfa(&specs, needs);
        assert!(
            check_dui_soundness("default", &dfa, &specs).is_ok(),
            "conformant backtick opener must pass"
        );
    }

    /// End-to-end: a modal grammar whose default mode has the "!" push/plain conflict
    /// is rejected by the REAL pipeline the `language!` macro drives — NFA → subset
    /// construction → minimisation → the mode-effect gate — not by calling
    /// [`check_dui_soundness`] on a hand-built DFA (which
    /// `dui_real_pipeline_same_pattern_conflict_rejected` above already does).
    ///
    /// ⚠ This used to be a `#[should_panic]` test. It is not any more, and could not
    /// stay one: this workspace builds the proc macro under cranelift
    /// (`[profile.dev] codegen-backend = "cranelift"`), where a `panic!` does not
    /// unwind across the `proc_macro` bridge — `rustc` aborts with
    /// `fatal runtime error: Rust cannot catch foreign exceptions` and prints
    /// nothing. What the test distinguishes is UNCHANGED and then some: before it
    /// could only tell "some panic whose message contains `DUI violation`" from "no
    /// panic"; it now separates rejection from acceptance on the same input, pins
    /// BOTH conflicting token names in the diagnostic, and — via the control below —
    /// requires the rejection to be attributable to the conflict rather than to
    /// running the pipeline at all.
    #[test]
    fn dui_generate_lexer_rejects_violation_grammar() {
        let input = LexerInput {
            language_name: "DuiViolation".to_string(),
            terminals: Vec::new(),
            needs: BuiltinNeeds::default(),
            literal_patterns: LiteralPatterns::default(),
            custom_tokens: vec![
                dui_spec("PushBang", "!", Some("inner"), false),
                dui_spec("PlainBang", "!", None, false),
            ],
            modes: vec![LexerModeInput {
                name: "inner".to_string(),
                custom_tokens: vec![dui_spec("CloseInner", "!", None, true)],
                raw: false,
            }],
            reserved_kinds: ReservedKeywords::default(),
        };
        let rejection = try_generate_lexer_as_string_hybrid(&input, false)
            .expect_err("the `!` push/plain conflict must be rejected end-to-end");
        assert!(
            rejection.contains("DUI violation"),
            "the pipeline rejected the grammar, but not as a DUI violation: {rejection}"
        );
        assert!(
            rejection.contains("PushBang") && rejection.contains("PlainBang"),
            "the diagnostic must name BOTH conflicting tokens, or it cannot be acted on: \
             {rejection}"
        );

        // ★ ANTI-VACUITY. Drop `PlainBang` — the ONLY change — and the same pipeline on
        // the same shape of input must SUCCEED. Without this cell the assertion above
        // would also be satisfied by a pipeline that rejects every modal grammar, or one
        // that fails for an unrelated reason and happens to mention the phrase.
        let conformant = LexerInput {
            custom_tokens: vec![dui_spec("PushBang", "!", Some("inner"), false)],
            ..input
        };
        let (code, _stats) = try_generate_lexer_as_string_hybrid(&conformant, false)
            .expect("removing the conflicting token must make the same grammar generable");
        assert!(
            !code.is_empty(),
            "the conformant control must actually emit a lexer, not an empty string"
        );
    }
}
