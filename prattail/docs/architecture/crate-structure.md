# PraTTaIL Crate Structure

**Module dependency graph and responsibilities for the `mettail-prattail` crate.**

---

## Overview

PraTTaIL (Pratt + Recursive Descent + Automata-Informed Lexing) is a parser generator
library that takes a `LanguageSpec` and produces a `proc_macro2::TokenStream` containing
a complete lexer and parser for that language. It is invoked by the `mettail-macros`
proc-macro crate during compilation of `language! { ... }` definitions.

The crate consists of 8 modules plus a test suite, organized into three subsystems:
the **lexer pipeline** (automata-based), the **parser pipeline** (Pratt + RD), and the
**pipeline orchestrator** (state machine coordinating both subsystems).

---

## Module Dependency Graph

```
                         ┌───────────┐
                         │  lib.rs   │
                         │ (types +  │
                         │  entry pt)│
                         └─────┊─────┘
                               │
                               ▼
                        ┌──────────────┐
                        │ pipeline.rs  │
                        │ (orchestrator│
                        │  + state     │
                        │  machine)    │
                        └──────┊───────┘
                               │
          ┌──────────┬─────────┼─────────┬──────────┐
          │          │         │         │          │
          ▼          ▼         ▼         ▼          ▼
    ┌─────────┐ ┌────────┐ ┌──────────┐ ┌────────┐ ┌──────────┐
    │ lexer.rs│ │binding_│ │prediction│ │ pratt  │ │recursive │
    │         │ │power.rs│ │   .rs    │ │  .rs   │ │  .rs     │
    └─────────┘ └────────┘ └──────────┘ └────────┘ └──────────┘
          │                      │          │           │
          ▼                      │          │           │
    ┌─────┊─────┐                │          ▼           │
    │ automata/ │                │     ┌──────────┐     │
    │ (mod.rs)  │                │     │dispatch  │     │
    └─────┊─────┘                │     │  .rs     │     │
          │                      │     └──────────┘     │
    ┌─────┼─────┬─────┬─────┐    │                      │
    │     │     │     │     │    │                      │
    ▼     ▼     ▼     ▼     ▼    │                      │
  nfa   part   sub   min   code  │                      │
  .rs   ition  set   imize gen   │                      │
        .rs    .rs   .rs   .rs   │                      │
                                 │                      │
                                 └──────────┬───────────┘
                                            │
                                       (FIRST/FOLLOW
                                        sets used by
                                        all parser
                                        modules)
```

### Detailed Dependency Arrows

```
lib.rs
  │
  └──→ pipeline.rs (orchestrator ── coordinates all modules below)
          │
          ├──→ lexer.rs ──────→ automata/mod.rs (types: TokenKind, TerminalPattern, etc.)
          │       │                  │
          │       │                  ├──→ automata/nfa.rs      (Thompson's + Aho-Corasick trie)
          │       │                  ├──→ automata/partition.rs (alphabet partitioning)
          │       │                  ├──→ automata/subset.rs    (NFA → DFA)
          │       │                  ├──→ automata/minimize.rs  (Hopcroft's minimization)
          │       │                  └──→ automata/codegen.rs   (DFA → Rust code as String)
          │       │
          │       ├──→ automata/codegen.rs (terminal_to_variant_name)
          │       ├──→ automata/minimize.rs (minimize_dfa)
          │       ├──→ automata/nfa.rs (build_nfa, BuiltinNeeds)
          │       ├──→ automata/partition.rs (compute_equivalence_classes)
          │       └──→ automata/subset.rs (subset_construction)
          │
          ├──→ binding_power.rs ──→ automata/codegen.rs (terminal_to_variant_name)
          │       (standalone analysis; no deps on other parser modules)
          │
          ├──→ prediction.rs ────→ automata/codegen.rs (terminal_to_variant_name)
          │       (FIRST sets, FOLLOW sets, nullable detection, dispatch tables,
          │        grammar warnings, sync predicate generation)
          │
          ├──→ pratt.rs ─────────→ binding_power.rs (BindingPowerTable)
          │       │                  prediction.rs (DispatchTable, FirstSet, sync predicates)
          │       └────────────────→ automata/codegen.rs (terminal_to_variant_name)
          │       (also generates: recovery helpers, recovering parsers, entry points)
          │
          ├──→ recursive.rs ─────→ automata/codegen.rs (terminal_to_variant_name)
          │       │                  pratt.rs (PrefixHandler)
          │       (produces PrefixHandler values consumed by pratt.rs)
          │
          └──→ dispatch.rs ──────→ automata/codegen.rs (terminal_to_variant_name)
                  │                  prediction.rs (CrossCategoryOverlap, FirstSet)
                  (uses FIRST set overlap analysis for backtracking decisions)
```

> **Terminology note:** "dispatch table" refers to the `DispatchTable` data
> structure built by `prediction.rs` (mapping tokens to parse actions). "Dispatch
> wrapper" refers to the generated `parse_<Cat>()` wrapper function produced by
> `dispatch.rs` (which handles cross-category backtracking before delegating to
> the Pratt parser).

---

## Module Responsibilities

### `lib.rs` -- Entry Point and Type Definitions

- **Public API**: `generate_parser(spec: &LanguageSpec) -> TokenStream`
  (delegates to `pipeline::run_pipeline`)
- **Data types**: `LanguageSpec`, `CategorySpec`, `RuleSpec`, `SyntaxItemSpec`,
  `CollectionKind`, `Associativity`
- `RuleSpec` fields include: `is_unary_prefix`, `is_postfix`, `prefix_precedence`,
  `associativity`, `eval_mode`, `has_rust_code`, `rust_code`
- `SyntaxItemSpec` variants: `Terminal`, `NonTerminal`, `IdentCapture`, `Binder`,
  `Collection`, `ZipMapSep`, `Optional`

### `pipeline.rs` -- Pipeline Orchestrator (State Machine)

- **State machine**: `PipelineState` enum with states:
  `Ready` → `Generated` → `Complete`
- **Public API**: `run_pipeline(spec: &LanguageSpec) -> TokenStream`
- **Send+Sync data bundles** (extracted from `!Send` `LanguageSpec`):
  - `LexerBundle` { grammar_rules, type_infos }
  - `ParserBundle` { categories, bp_table, rule_infos, follow_inputs, rd_rules,
    cross_rules, cast_rules }
- **Extraction**: `extract_from_spec()` converts `LanguageSpec` into bundles,
  handling terminal collection, mixfix part extraction, and RD syntax conversion
- **Code generation**: calls lexer and parser codegen, builds a single `String` buffer,
  then calls `str::parse::<TokenStream>()` once at the end
- Rayon parallelism was tested and rejected (81-197% regression under `taskset -c 0`)

### `automata/mod.rs` -- Core Types

- `StateId` (u32), `ClassId` (u8), `DEAD_STATE` sentinel
- `Span` (start, end positions)
- `TokenKind` enum (Eof, Ident, Integer, Float, True, False, StringLit, Fixed, Dollar, DoubleDollar)
- `CharClass` (Single, Range, Class)
- `NfaState`, `Nfa`, `NfaFragment` -- NFA representation
- `DfaState`, `Dfa` -- DFA representation (dense `Vec<StateId>` transitions)
- `TerminalPattern` -- grammar terminal ready for NFA construction

### `automata/nfa.rs` -- Thompson's Construction + Aho-Corasick Keyword Trie

- `build_nfa(terminals, needs) -> Nfa`
- `build_keyword_trie(nfa, terminals) -> StateId` -- builds prefix-sharing trie
  directly into the NFA, replacing per-terminal epsilon chains for fixed terminals.
  Single epsilon from `global_start` to `trie_root` (vs N epsilons for N terminals).
- `BuiltinNeeds` -- which character-class patterns (ident, integer, float, string) are needed
- Builds fragments for identifiers, integers, floats, string literals
- `build_string_fragment()` retained as `#[cfg(test)]` only (for unit tests)
- `epsilon_closure(nfa, states) -> Vec<StateId>` for subset construction

### `automata/partition.rs` -- Alphabet Equivalence Classes

- `compute_equivalence_classes(nfa) -> AlphabetPartition`
- Partitions 256 ASCII byte values into equivalence classes
- Bytes that trigger identical transitions in every NFA state are grouped together
- Typically reduces 256 columns to 12-18 equivalence classes (~15-20x compression)
- `AlphabetPartition` contains `byte_to_class: [ClassId; 256]` lookup table

### `automata/subset.rs` -- Subset Construction (NFA to DFA)

- `subset_construction(nfa, partition) -> Dfa`
- Standard powerset algorithm using equivalence classes instead of raw bytes
- DFA accept states inherit highest-priority token kind from NFA state sets
- Uses `HashMap<Vec<StateId>, StateId>` for O(1) state set lookups
- Eliminates all epsilon transitions

### `automata/minimize.rs` -- True Hopcroft's DFA Minimization

- `minimize_dfa(dfa) -> Dfa`
- True Hopcroft's algorithm with inverse transition map
- Pre-built `inverse[target][class_id]` for O(1) predecessor lookup
- `partition_of: Vec<usize>` for O(1) state-to-partition mapping
- Accept grouping via `BTreeMap<Option<&TokenKind>, Vec<StateId>>` (no `format!` allocations)
- O(n log n) on number of DFA states
- Start state is always remapped to state 0

### `automata/codegen.rs` -- DFA to Rust Code (String-Based)

- `generate_lexer_string(dfa, partition, token_kinds, language_name) -> String`
- Builds entire lexer as a `String` buffer; no intermediate `TokenStream` allocations
- Two strategies:
  - **Direct-coded** (DFA states <= 30): each state is a match arm in `dfa_next()`
  - **Table-driven** (DFA states > 30): flat `TRANSITIONS` array with row indexing
- Generates `Token<'a>` enum with zero-copy borrowed fields:
  `Ident(&'a str)`, `StringLit(&'a str)`, `Dollar(&'a str)`, `DoubleDollar(&'a str)`
- Generates `Position` and `Range` structs for structured source locations
- Generates `ParseError` enum: `UnexpectedToken`, `UnexpectedEof`, `TrailingTokens`, `InvalidLiteral`
- `terminal_to_variant_name(terminal) -> String` converts operator strings to Rust
  identifiers (e.g., `"+"` → `"Plus"`, `"error"` → `"KwError"`)

### `lexer.rs` -- Lexer Pipeline Orchestrator

- `generate_lexer(input) -> (TokenStream, LexerStats)`
- `generate_lexer_as_string(input) -> (String, LexerStats)` (used by pipeline)
- `extract_terminals(grammar_rules, type_infos) -> LexerInput`
- Chains: terminals → NFA (with Aho-Corasick trie) → partition → DFA → minimize → codegen
- Detects native types (i32/i64 → integer, f64 → float, bool → boolean, String → string)
- Injects `true`/`false` keyword terminals for bool types
- Returns pipeline statistics (NFA/DFA/minimized state counts, equivalence class count)

### `binding_power.rs` -- Binding Power Analysis (Standalone)

- `analyze_binding_powers(rules) -> BindingPowerTable`
- Classifies infix, postfix, and mixfix operators by category and declaration order
- **Associativity** enum: `Left`, `Right`
- **Two-pass binding power assignment**:
  1. Non-postfix operators: assigned in declaration order, precedence increments by 2
  2. Postfix operators: assigned at `max_non_postfix_bp + 4+`
- **Binding power pairs**:
  - Left-associative: `left_bp < right_bp` (e.g., (2, 3) for `+`)
  - Right-associative: `left_bp > right_bp` (e.g., (7, 6) for `^`)
  - Postfix: `(postfix_bp, 0)` with `postfix_bp > max_non_postfix_bp`
- **MixfixPart** struct: `{ operand_category, param_name, following_terminal }`
  for N-ary operators (e.g., ternary `a ? b : c`)
- `InfixOperator` includes `is_postfix`, `is_mixfix`, `mixfix_parts` fields
- `BindingPowerTable` generates `infix_bp()`, `make_infix()`, `postfix_bp()`,
  `make_postfix()`, `mixfix_bp()`, `handle_mixfix()` functions

### `prediction.rs` -- FIRST Sets, FOLLOW Sets, Dispatch Tables, and Grammar Warnings

- `compute_first_sets(rules, categories) -> BTreeMap<String, FirstSet>`
- `compute_follow_sets_from_inputs(inputs, categories, first_sets, primary) -> BTreeMap<String, FirstSet>`
- `build_dispatch_tables(rules, categories, first_sets) -> BTreeMap<String, DispatchTable>`
- `analyze_cross_category_overlaps(categories, first_sets) -> BTreeMap<..., Overlap>`
- `detect_grammar_warnings(rules, categories, all_syntax) -> Vec<GrammarWarning>`
- `generate_sync_predicate(buf, category, follow_set, grammar_terminals)` -- per-category
  sync predicates for error recovery (FOLLOW + structural delimiters)
- **Nullable detection**: `FirstSet.nullable` flag computed during FIRST set iteration
- **GrammarWarning** enum: `AmbiguousPrefix`, `LeftRecursion`, `UnusedCategory`
- Fixed-point iteration for FIRST set computation (handles transitive nonterminal references)
- FIRST sets augmented with native literal tokens (Integer, Boolean, etc.)
- Dispatch actions: Direct, Lookahead, CrossCategory, Cast, Grouping, Variable
- `generate_first_set_check(first_set, token_var) -> TokenStream` for inline FIRST tests

### `pratt.rs` -- Pratt Expression Parser Generation

- `write_pratt_parser(buf, config, bp_table, prefix_handlers)` -- Pratt parser per category
- `write_parser_helpers(buf)` -- expect_token, expect_ident, peek_token, peek_ahead
  (two lifetimes `<'a, 'b>` on peek functions for zero-copy)
- `write_recovery_helpers(buf)` -- sync_to, expect_token_rec, expect_ident_rec
- `write_pratt_parser_recovering(buf, config, bp_table)` -- recovery-aware Pratt parser
- `write_dispatch_recovering(buf, category)` -- recovery entry point wrapper
- Per category: `parse_<Cat>()` (Pratt loop), `parse_<Cat>_prefix()` (prefix handler)
- Postfix support: `write_postfix_bp_function()`, `write_make_postfix()`
- Mixfix support: `write_mixfix_bp_function()`, `write_handle_mixfix()`
- `PrattConfig` controls: category, primary status, infix/postfix/mixfix existence,
  native_type, cast_rules, own_first_set, all_first_sets, follow_set
- `PrefixHandler` struct: category, label, match_arm (String), ident_lookahead, parse_fn_name
- Entry points per category (4 total):
  1. `Cat::parse(input)` -- fail-fast, returns `Result<Cat, String>`
  2. `Cat::parse_with_file_id(input, file_id)` -- fail-fast with file tracking
  3. `Cat::parse_recovering(input)` -- multi-error, returns `(Option<Cat>, Vec<ParseError>)`
  4. `Cat::parse_recovering_with_file_id(input, file_id)` -- multi-error with file tracking

### `recursive.rs` -- Recursive Descent Handler Generation

- `write_rd_handler(buf, rule) -> PrefixHandler`
- Handles structural constructs: binders, collections, pattern operations, multi-token syntax
- `RDRuleInfo` carries rule details (label, category, items, has_binder, has_multi_binder,
  is_collection, collection_type, separator, prefix_bp, eval_mode)
- `RDSyntaxItem` variants:
  Terminal, NonTerminal, IdentCapture, Binder, Collection, SepList, ZipMapSep, Optional
- `CollectionKind`: HashBag, HashSet, Vec
- Generates parse function bodies with captures and constructors
- Supports single binders (Scope), multi-binders (Vec of Binders), HOL native Rust code blocks

### `dispatch.rs` -- Cross-Category Dispatch

- `write_category_dispatch(buf, category, cross_rules, cast_rules, overlaps, first_sets)`
- Wraps the core Pratt parser with cross-category logic:
  - Tokens unique to source category → deterministic cross-category parse
  - Ambiguous tokens (in both FIRST sets) → save/restore backtracking
  - Cast rules → parse source category and wrap in target constructor
- `CrossCategoryRule`: source/result categories, operator, backtrack flag
- `CastRule`: source/target categories, wrapper constructor label

---

## External Dependencies

```
proc-macro2   -- TokenStream representation (used only for final str::parse())
quote         -- (dev-dependency only; removed from critical path by string-based codegen)
syn           -- (dev-dependency via workspace, used by macros crate)
```

**Note:** The `quote` crate and `proc-macro2` token-by-token construction were removed
from the codegen hot path in the string-based codegen migration (Phase 2+3). The only
remaining use of `proc-macro2` is the single `str::parse::<TokenStream>()` call at the
end of `pipeline.rs` which converts the complete generated-code string into a TokenStream.

---

## Test Modules

```
tests/
  mod.rs                -- test suite entry point
  automata_tests.rs     -- NFA/DFA pipeline: lexing, Aho-Corasick trie construction (9 tests)
  lexer_tests.rs        -- terminal extraction, lexer code generation, pipeline stats (4 tests)
  prediction_tests.rs   -- FIRST sets, FOLLOW sets, dispatch tables, cross-category overlap (12 tests)
  integration_tests.rs  -- full generate_parser() for Calculator, TypedCalc specs (8 tests)
  error_tests.rs        -- codegen-level + end-to-end error case tests (13 tests)
  recovery_tests.rs     -- panic-mode error recovery: codegen + end-to-end (11 tests)
  warning_tests.rs      -- grammar warning detection: ambiguous prefix, left recursion, unused (12 tests)
```

Additional unit tests are embedded in source modules:
- `automata/nfa.rs`: 11 tests (trie construction, fragment building)
- `automata/minimize.rs`: 2 tests
- `automata/partition.rs`: 1 test
- `automata/subset.rs`: 2 tests
- `automata/codegen.rs`: 1 test

**Total**: 86 tests within the `mettail-prattail` crate (69 in test modules + 17 in source modules).

---

## Data Flow Summary

```
LanguageSpec
    │
    ▼
[pipeline.rs: extract_from_spec()]
    │
    ├──→ LexerBundle  ──→ [lexer pipeline]     ──→ String (Token<'a> enum + lex function)
    ├──→ ParserBundle
    │       │
    │       ├──→ [binding power]       ──→ BindingPowerTable (infix, postfix, mixfix)
    │       ├──→ [prediction]          ──→ FirstSets + FollowSets + DispatchTables + Overlaps
    │       ├──→ [grammar warnings]    ──→ Vec<GrammarWarning> (compile-time diagnostics)
    │       ├──→ [recursive descent]   ──→ Vec<PrefixHandler> + String (RD function bodies)
    │       ├──→ [pratt generation]    ──→ String (per-category Pratt parsers)
    │       ├──→ [recovery generation] ──→ String (sync predicates + recovering parsers)
    │       └──→ [cross-category]      ──→ String (dispatch wrappers)
    │
    └──→ [assembly: single str::parse::<TokenStream>()] ──→ TokenStream (complete parser)
```
