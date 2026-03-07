# PraTTaIL: Architecture Overview

**Date:** 2026-03-03

---

## Table of Contents

1. [High-Level Data Flow](#1-high-level-data-flow)
2. [Pipeline Stages](#2-pipeline-stages)
3. [Module Structure](#3-module-structure)
4. [Data Types and Interfaces](#4-data-types-and-interfaces)
5. [Code Generation Assembly](#5-code-generation-assembly)
6. [Worked Example: End-to-End Flow](#6-worked-example-end-to-end-flow)
7. [Language Composition Entry Points](#7-language-composition-entry-points)

---

## 1. High-Level Data Flow

The PraTTaIL pipeline transforms a `LanguageSpec` (the serializable
representation of a `language!` macro invocation) into a `TokenStream`
containing a complete, self-contained parser. Three composition entry points
feed into the pipeline: `language!` (primary), `language_fragment!` (reusable
fragments), and `compose_languages!` (runtime delegation).

The pipeline is organized as a three-phase state machine:
`Extract` -> `Generate` -> `Finalize`, represented by the `PipelineState`
enum in `pipeline.rs`.

```
  language! { ... }       language_fragment! { ... }       compose_languages! { ... }
        │                         │                                   │
        │   extends:/includes:/   │   mixins:                         │
        │   mixins: resolution    │   registry                        │
        ▼                         ▼                                   ▼
  ┌───────────────────────────────────┐                   ┌───────────────────────┐
  │         macros crate              │                   │ compose_gen.rs        │
  │         (proc-macro)              │                   │ {Name}TermInner enum  │
  │                                   │                   │ {Name}Term wrapper    │
  │  Parse DSL syntax                 │                   │ {Name}Env struct      │
  │  Resolve extends/includes/mixins  │                   │ {Name}Language impl   │
  │  merge_language_defs()            │                   │ Delegation parsing    │
  │  Build LanguageDef                │                   └───────────┬───────────┘
  │  Project to LanguageSpec          │                               │
  └────────────────┬──────────────────┘                               ▼
                   │                                           TokenStream
                   ▼                                        (composed runtime)
        ┌─────────────────────────────────┐
        │ LanguageSpec {                  │
        │   name, types, rules,           │
        │   beam_width, literal_patterns, │
        │   recovery_config,              │
        │   semantic_dependency_groups,   │
        │ }                               │
        └──────────┬──────────────────────┘
                   │
                   ▼
   ┌───────────────────────────────────────────────────────────────┐
   │  PraTTaIL Pipeline State Machine (pipeline.rs)                │
   │                                                               │
   │    ┌─────────────────────┐                                    │
   │    │   [Extract Phase]   │  extract_from_spec()               │
   │    │                     │                                    │
   │    │  Single pass over   │                                    │
   │    │  LanguageSpec.rules │                                    │
   │    └──────────┬──────────┘                                    │
   │               │                                               │
   │               ▼                                               │
   │  ┌────────────────────────────────┐                           │
   │  │ PipelineState::Ready {         │                           │
   │  │   lexer_bundle: LexerBundle,   │                           │
   │  │   parser_bundle: ParserBundle, │                           │
   │  │ }                              │                           │
   │  └────────────┬───────────────────┘                           │
   │               │                                               │
   │               ▼                                               │
   │    ┌──────────────────────────────────────────┐               │
   │    │          [Generate Phase]                │               │
   │    │                                          │               │
   │    │  ┌──────────────────┐ ┌────────────────┐ │               │
   │    │  │ Lexer Pipeline   │ │ Parser Pipeline│ │               │
   │    │  │                  │ │                │ │               │
   │    │  │ Terminal Extract │ │ FIRST/FOLLOW   │ │               │
   │    │  │ NFA -> DFA ->    │ │ BP Table       │ │               │
   │    │  │ Minimize ->      │ │ Prediction     │ │               │
   │    │  │ Equiv Classes -> │ │ WFST           │ │               │
   │    │  │ Codegen          │ │ Dead-rule      │ │               │
   │    │  │        │         │ │ Lint layer     │ │               │
   │    │  │        ▼         │ │ Trampoline     │ │               │
   │    │  │ lexer_code: Str  │ │ Dispatch       │ │               │
   │    │  │ variant_map      │ │        │       │ │               │
   │    │  │ ambiguity_info   │ │        ▼       │ │               │
   │    │  └──────────────────┘ │ parser_code    │ │               │
   │    │                       └────────────────┘ │               │
   │    └───────────────────┬──────────────────────┘               │
   │                        │                                      │
   │                        ▼                                      │
   │  ┌────────────────────────────┐                               │
   │  │ PipelineState::Generated { │                               │
   │  │   lexer_code: String,      │                               │
   │  │   parser_code: String,     │                               │
   │  │ }                          │                               │
   │  └────────────────────┬───────┘                               │
   │                       │                                       │
   │                       ▼                                       │
   │    ┌──────────────────────────────┐                           │
   │    │     [Finalize Phase]         │                           │
   │    │                              │                           │
   │    │  combined = lexer_code       │                           │
   │    │           + parser_code      │                           │
   │    │  combined.parse::<           │                           │
   │    │    TokenStream>()            │                           │
   │    └──────────────┬───────────────┘                           │
   │                   │                                           │
   │                   ▼                                           │
   │    PipelineState::Complete(TokenStream)                       │
   │                                                               │
   └───────────────────────────────┬───────────────────────────────┘
                                   │
                                   ▼
                             TokenStream
                          (Rust source code)
```

## 2. Pipeline Stages

The pipeline is a three-phase state machine implemented by the `PipelineState`
enum in `pipeline.rs`. Each phase transitions the state to the next via
`advance()`. The two primary entry points are:

- `generate_parser(spec) -> TokenStream`
- `generate_parser_with_analysis(spec) -> (TokenStream, PipelineAnalysis)`

### Phase 1: Extract

**Entry:** `extract_from_spec(&LanguageSpec) -> (LexerBundle, ParserBundle)`

A single pass over `spec.rules` builds all collections needed by both the
lexer and parser pipelines. The resulting bundles are `Send + Sync` (they
do not contain `proc_macro2::TokenStream` fields), enabling future
parallelism if codegen workload becomes large enough to justify thread
overhead.

| Output         | Contents                                                                                                                                                                                                                       |
|----------------|--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `LexerBundle`  | `grammar_rules`, `type_infos`, `has_binders`, `category_names`, `literal_patterns`                                                                                                                                             |
| `ParserBundle` | `grammar_name`, `categories`, `bp_table`, `rule_infos`, `follow_inputs`, `rd_rules`, `cross_rules`, `cast_rules`, `has_binders`, `beam_width`, `recovery_config`, `all_syntax`, `rule_locations`, `semantic_dependency_groups` |
|                |                                                                                                                                                                                                                                |

State transition: `LanguageSpec` -> `PipelineState::Ready { lexer_bundle, parser_bundle }`

### Phase 2: Generate

**Lexer codegen:** `generate_lexer_code_with_map(&LexerBundle) -> (String, TokenVariantMap, LexerAmbiguityInfo)`

Sub-steps:
1. Terminal extraction (`extract_terminals`)
2. NFA construction (Thompson's construction)
3. Subset construction (NFA -> DFA)
4. DFA minimization (Hopcroft's algorithm)
5. Equivalence class computation
6. Direct-coded lexer codegen (IS_ACCEPTING bitmap, lex_core/lex_weighted_core)

**Parser codegen:** `generate_parser_code_with_context(&ParserBundle, &TokenVariantMap, &LexerAmbiguityInfo) -> String`

Sub-steps:
1. FIRST set computation (fixed-point iteration)
2. FOLLOW set computation
3. Binding power table analysis (infix, prefix, postfix, mixfix)
4. Prediction WFST construction per category (tropical shortest-path)
5. Dead-rule detection (5-tier: LiteralNoNativeType, UnreachableCategory, WfstUnreachable, SemanticLiveness, WpdsStackAware)
6. Inter-category dead-path detection (BooleanWeight forward-backward)
7. Nearly-dead path detection (ProductWeight<BooleanWeight, CountingWeight>)
8. Lint layer execution (diagnostics across 7 categories: G, W, R, C, D, P, COMP)
9. Recursive descent handler generation
10. Trampolined parser generation (Frame_Cat enums, explicit continuation stack)
11. Cross-category dispatch generation (WFST-weight-ordered match arms)
12. Error recovery codegen (WFST-weighted repair actions)
13. EBNF debug dump (opt-in via `PRATTAIL_DUMP_EBNF` environment variable)

State transition: `PipelineState::Ready` -> `PipelineState::Generated { lexer_code, parser_code }`

### Phase 3: Finalize

**Concatenation and parse:** `lexer_code + parser_code` -> `str::parse::<TokenStream>()`

State transition: `PipelineState::Generated` -> `PipelineState::Complete(TokenStream)`

### Phase Dependencies

```
  Lexer Codegen (NFA -> DFA -> Minimize -> Equiv Classes)
         │
         │  variant_map, ambiguity_info
         │
         ▼
  Parser Codegen (FIRST/FOLLOW -> BP -> WFST -> Lint -> Trampoline -> Dispatch)
         │
         ▼
  Finalize (concatenate + parse into TokenStream)
```

The lexer must complete before parser codegen begins because the parser
needs the `TokenVariantMap` (token variant names for match arms) and
`LexerAmbiguityInfo` (multi-accept DFA states for disambiguation).

## 3. Module Structure

```
prattail/src/
  |
  |-- lib.rs                 Top-level orchestration, LanguageSpec types,
  |                          generate_parser() and generate_parser_with_analysis()
  |                          entry points, PipelineAnalysis export struct
  |
  |-- pipeline.rs            PipelineState state machine (Ready/Generated/Complete),
  |                          extract_from_spec(), run_pipeline(),
  |                          run_pipeline_with_analysis(),
  |                          dead-rule detection (4-tier), inter-category dead-path
  |                          analysis (A4), nearly-dead path detection (A8),
  |                          LexerBundle, ParserBundle, CategoryInfo
  |
  |-- lexer.rs               Lexer pipeline orchestration:
  |                          extract_terminals(), generate_lexer_as_string()
  |
  |-- automata/
  |     |-- mod.rs           Core types: StateId, ClassId, NfaState,
  |     |                    DfaState, Nfa, Dfa, CharClass, TokenKind,
  |     |                    TerminalPattern, NfaFragment
  |     |
  |     |-- nfa.rs           Thompson's construction: build_nfa(),
  |     |                    build_string_fragment(), build_ident_fragment(),
  |     |                    build_integer_fragment(), etc.
  |     |                    Epsilon closure computation.
  |     |
  |     |-- partition.rs     Alphabet equivalence class computation:
  |     |                    compute_equivalence_classes(), AlphabetPartition
  |     |
  |     |-- subset.rs        Subset construction (NFA -> DFA):
  |     |                    subset_construction(), dfa_transition()
  |     |
  |     |-- minimize.rs      Hopcroft's DFA minimization:
  |     |                    minimize_dfa()
  |     |
  |     |-- codegen.rs       Lexer code generation:
  |     |                    generate_lexer_code(), Token enum generation,
  |     |                    IS_ACCEPTING bitmap (u128 or bool array),
  |     |                    terminal_to_variant_name(), TokenVariantMap,
  |     |                    LexerAmbiguityInfo
  |     |
  |     |-- regex.rs         Configurable literal pattern compiler:
  |     |                    parse_literal_patterns_ebnf(), PCRE-subset -> NFA
  |     |
  |     +-- semiring.rs      Semiring trait + semiring types:
  |                          TropicalWeight, CountingWeight, BooleanWeight,
  |                          EditWeight, ProductWeight, ComplexityWeight (always-on),
  |                          LogWeight (wfst-log feature only)
  |
  |-- prediction.rs          FIRST set computation (fixed-point iteration),
  |                          FOLLOW set computation, dispatch table construction,
  |                          cross-category overlap analysis, FirstSet, RuleInfo,
  |                          FollowSetInput
  |
  |-- binding_power.rs       Binding power table construction,
  |                          infix_bp / make_infix code generation,
  |                          Associativity enum, MixfixPart
  |
  |-- trampoline.rs          Stack-safe trampolined parser generation:
  |                          Frame_Cat enums (one per category), explicit
  |                          continuation stack (Vec<Frame>),
  |                          write_trampolined_parser(),
  |                          write_trampolined_parser_recovering(),
  |                          TrampolineConfig, thread-local frame pooling
  |
  |-- pratt.rs               Pratt parser code generation per category:
  |                          main Pratt loop, prefix handler dispatch,
  |                          parse entry points, helper functions,
  |                          PrefixHandler
  |
  |-- recursive.rs           Recursive descent handler generation:
  |                          per-rule parse functions for structural
  |                          constructs (binders, collections, Sep/Map/Zip),
  |                          RDRuleInfo, RDSyntaxItem, CollectionKind
  |
  |-- dispatch.rs            Cross-category dispatch generation:
  |                          cast rules, cross-category rules,
  |                          FIRST-set-driven backtracking decisions,
  |                          WFST-weight-ordered match arms,
  |                          CastRule, CrossCategoryRule
  |
  |-- lint.rs                Unified compile-time lint layer:
  |                          diagnostics across 7 categories (G, W, R, C,
  |                          D, P, COMP), LintContext, run_lints(),
  |                          LintDiagnostic, LintSeverity,
  |                          Rust-compiler-style output
  |
  |-- runtime_types.rs       Shared runtime types (imported by generated code
  |                          via `use mettail_prattail::runtime_types::*`):
  |                          Position, Range, ParseError,
  |                          lex_core(), lex_weighted_core() generic lex loops,
  |                          is_whitespace()
  |
  |-- classify.rs            Automatic rule classification from syntax items:
  |                          classify_rule() -> RuleClassification (is_infix,
  |                          is_postfix, is_unary_prefix, is_var, is_literal,
  |                          is_cast, is_cross_category, etc.)
  |
  |-- wfst.rs                WFST prediction engine (always-on):
  |                          PredictionWfst, predict(), predict_pruned(),
  |                          predict_with_confidence(), CSR serialization,
  |                          WeightedAction, WeightedTransition
  |
  |-- token_id.rs            Compact token-to-integer mapping for
  |                          WFST state indexing (TokenIdMap, Arc<str> interning)
  |
  |-- lattice.rs             Token lattice and Viterbi decoding:
  |                          TokenLattice<T,S,W>, viterbi_best_path(),
  |                          viterbi_best_path_beam(), n_best_paths(),
  |                          viterbi_generic<W: Semiring + Ord>(),
  |                          linear_to_lattice_generic<W>()
  |
  |-- recovery.rs            WFST-weighted error recovery:
  |                          RepairAction, RecoveryWfst, RecoveryConfig,
  |                          edit_cost(), find_recovery(),
  |                          find_recovery_contextual(),
  |                          ParseSimulator, SimulationResult
  |
  |-- compose.rs             WFST product construction:
  |                          compose_wfsts() for combining transducers
  |
  |-- composition_optimize.rs Composition-specific WFST optimizations
  |
  |-- composition_verify.rs  Composition correctness verification
  |
  |-- cost_benefit.rs        Cost-benefit analysis framework for
  |                          optimization decision-making
  |
  |-- prefix_trie.rs         Prefix trie for efficient terminal lookup
  |
  |-- transducer.rs          Finite-state transducer types and operations
  |
  |-- ebnf.rs                EBNF grammar dump (opt-in via PRATTAIL_DUMP_EBNF)
  |
  |-- forward_backward.rs    Forward-backward algorithm (always-on, generic
  |                          over any semiring). Used by A4 (BooleanWeight)
  |                          and A8 (ProductWeight<BooleanWeight, CountingWeight>)
  |
  |-- log_push.rs            Log weight pushing (wfst-log feature only)
  |-- training.rs            Model training (wfst-log feature only)
  |-- grammar_gen.rs         Grammar generation (grammar-gen feature only)
  |
  +-- tests/
        |-- mod.rs
        |-- automata_tests.rs
        |-- lexer_tests.rs
        |-- prediction_tests.rs
        +-- integration_tests.rs
```

## 4. Data Types and Interfaces

### Input Types (from macros crate)

```
LanguageSpec
  |-- name: String                       "Calculator"
  |-- types: Vec<CategorySpec>
  |     |-- name: String                 "Int", "Bool", "Str"
  |     |-- native_type: Option<String>  Some("i32"), Some("bool"), ...
  |     +-- is_primary: bool             true (first), false (rest)
  |-- rules: Vec<RuleSpec>
  |     |-- label: String                "Add", "Eq", "PZero"
  |     |-- category: String             "Int", "Bool", "Proc"
  |     |-- syntax: Vec<SyntaxItemSpec>
  |     |     Terminal(String)            "+", "{}", "error"
  |     |     NonTerminal { category, param_name }
  |     |     IdentCapture { param_name }
  |     |     Binder { param_name, category, is_multi }
  |     |     Collection { param_name, element_category, separator, kind }
  |     |     Sep { body, separator, kind }
  |     |     Map { body_items }
  |     |     Zip { left_name, right_name, left_category, right_category, body }
  |     |     BinderCollection { param_name, separator }
  |     |     Optional { inner }
  |     |-- is_infix: bool
  |     |-- associativity: Associativity (Left | Right)
  |     |-- is_unary_prefix: bool        true for "not" a, "-" a
  |     |-- prefix_precedence: Option<u8> overrides default max_infix_bp + 2
  |     |-- is_postfix: bool             true for a "!", a "?", a "++"
  |     |-- is_var, is_literal, is_cast, is_cross_category, ...
  |     |-- has_binder, has_multi_binder, is_collection, ...
  |     |-- rust_code: Option<TokenStream>
  |     |-- eval_mode: Option<String>
  |     +-- source_location: Option<SourceLocation>
  |-- beam_width: BeamWidthConfig        Disabled | Explicit(f64) | Auto
  |-- log_semiring_model_path: Option<String>
  |-- literal_patterns: LiteralPatterns  integer, float, string, ident regexes
  |-- recovery_config: RecoveryConfig    costs, thresholds, beam width
  +-- semantic_dependency_groups: Vec<HashSet<String>>
```

### SyntaxItemSpec Variants

The `SyntaxItemSpec` enum defines the building blocks of rule syntax.
The decomposed `Sep`, `Map`, and `Zip` variants replace the former monolithic
`ZipMapSep` and enable new compositions:

| Variant                                                              | Purpose                                                          |
|----------------------------------------------------------------------|------------------------------------------------------------------|
| `Terminal(String)`                                                   | Literal token to match                                           |
| `NonTerminal { category, param_name }`                               | Recursive parse of another category                              |
| `IdentCapture { param_name }`                                        | Capture an identifier                                            |
| `Binder { param_name, category, is_multi }`                          | Lambda binder position                                           |
| `Collection { param_name, element_category, separator, kind }`       | Simple separated collection                                      |
| `Sep { body, separator, kind }`                                      | Repeat body with separator; body can be NonTerminal, Map, or Zip |
| `Map { body_items }`                                                 | Structured body pattern (multi-item sequence)                    |
| `Zip { left_name, right_name, left_category, right_category, body }` | Dual-accumulator parallel collection                             |
| `BinderCollection { param_name, separator }`                         | Separated list of binder identifiers                             |
| `Optional { inner }`                                                 | Save/restore block; continues if inner fails                     |

Composition examples enabled by the decomposition:
- `Sep(Map(...))` -- structured separated list (single accumulator)
- `Sep(Zip { body: Map { .. } })` -- dual-accumulator structured list
- `Sep(NonTerminal)` -- simple separated list
- Standalone `Map` -- inline sequence of items
- Standalone `Zip` -- parallel dual-accumulator without separator

### Key Intermediate Types

```
LexerBundle                              Send+Sync data for lexer codegen
  |-- grammar_rules: Vec<GrammarRuleInfo>
  |-- type_infos: Vec<TypeInfo>
  |-- has_binders: bool
  |-- category_names: Vec<String>
  +-- literal_patterns: LiteralPatterns

ParserBundle                             Send+Sync data for parser codegen
  |-- grammar_name: String
  |-- categories: Vec<CategoryInfo>
  |-- bp_table: BindingPowerTable
  |-- rule_infos: Vec<RuleInfo>
  |-- follow_inputs: Vec<FollowSetInput>
  |-- rd_rules: Vec<RDRuleInfo>
  |-- cross_rules: Vec<CrossCategoryRule>
  |-- cast_rules: Vec<CastRule>
  |-- has_binders: bool
  |-- beam_width: BeamWidthConfig
  |-- recovery_config: RecoveryConfig
  |-- all_syntax: Vec<(String, String, Vec<SyntaxItemSpec>)>
  |-- rule_locations: HashMap<(String, String), SourceLocation>
  +-- semantic_dependency_groups: Vec<HashSet<String>>

BindingPowerTable                        Per-operator binding powers
  +-- operators: Vec<InfixOperator>
        |-- terminal, category, label
        |-- left_bp, right_bp
        |-- is_postfix, is_mixfix
        +-- mixfix_parts: Vec<MixfixPart>

FirstSet                                 Set of token variant names
  +-- tokens: HashSet<String>

PredictionWfst                           WFST-based dispatch prediction
  |-- predict(token) -> Vec<WeightedAction>
  |-- predict_pruned(token, beam) -> Vec<WeightedAction>
  +-- predict_with_confidence(token) -> Vec<(WeightedAction, f64)>

PipelineAnalysis                         Exported analysis for Ascent optimization
  |-- dead_rule_labels: HashSet<String>
  |-- unreachable_categories: HashSet<String>
  |-- constructor_weights: HashMap<String, f64>
  |-- category_weights: HashMap<String, f64>
  |-- isomorphic_groups: Vec<Vec<String>>
  +-- isomorphic_action_maps: Vec<HashMap<u32, Vec<(String, String)>>>
```

## 5. Code Generation Assembly

The Finalize phase concatenates lexer and parser code strings and parses
the combined result into a single `TokenStream`. The generated code is
structured as follows:

```
// ---- Shared Runtime Types ----
//   (imported from mettail_prattail::runtime_types)
//   Position, Range, ParseError, lex_core(), lex_weighted_core()

use mettail_prattail::runtime_types::*;

// ---- Lexer ----
//   Token enum (Eof, Ident, Integer, Plus, Star, ...)
//   CHAR_CLASS equivalence class table
//   IS_ACCEPTING bitmap (u128 or bool array)
//   Lexer struct with lex(), dfa_next(), accept_token()
//   Generated code calls lex_core()/lex_weighted_core() from runtime_types

#lexer_code

// ---- Trampolined Parsers (per category) ----
//   For each category Cat:
//     enum Frame_Cat { ... }     -- continuation frames
//     fn parse_Cat()             -- trampolined parser (explicit stack)
//     fn parse_Cat_recovering()  -- error-recovering variant
//
//   Frame variants cover: infix continuations, RD rule steps,
//   collection elements, binder bodies, Sep/Map/Zip iterations,
//   cross-category dispatch, cast backtrack, postfix check

#trampolined_parsers

// ---- Cross-Category Dispatch ----
//   Dispatch wrappers for categories with cross-category/cast rules
//   WFST-weight-ordered match arms
//   Deterministic (unique-to-source) and ambiguous (save/restore) paths

#dispatch_code

// ---- Prediction WFST Static Data ----
//   PREDICTION_{CAT}_STATES: &[...] -- CSR state offsets
//   PREDICTION_{CAT}_ARCS: &[...]   -- CSR arc (target, weight, action)

#prediction_wfst_data

// ---- Error Recovery ----
//   SYNC predicates per category (from FOLLOW sets)
//   Recovery helpers: find_sync_token(), try_repair()

#recovery_code
```

## 6. Worked Example: End-to-End Flow

Consider a minimal Calculator with `Int` (i32), `Bool` (bool), and rules
`Add`, `Eq`, `NumLit`, `BoolLit`, `IVar`, `BVar`.

**Extract Phase.** A single pass over rules builds:
- `LexerBundle`: terminal strings `+`, `==`; type infos for `i32`, `bool`
- `ParserBundle`: rule infos, BP table, RD rules, cross rules, cast rules

**Generate Phase -- Lexer.** Scans rules for terminal strings:
`+`, `==`. Detects native types: `i32` -> needs integer, `bool` -> needs
boolean (adds `true`/`false` keywords). Builds NFA, DFA, minimizes,
generates lexer with Token enum: `{Eof, Ident, Integer, Boolean, Plus, EqEq}`.
IS_ACCEPTING bitmap covers all accepting DFA states. `lex_core()` from
`runtime_types` provides the generic DFA loop.

**Generate Phase -- Binding Powers.** `Add` is infix in `Int`:
`+` gets `(left_bp=2, right_bp=3)` (left-associative).

**Generate Phase -- Prediction.** Computes FIRST sets:
- `FIRST(Int) = {Ident, Integer, LParen}`
- `FIRST(Bool) = {Ident, KwTrue, KwFalse, LParen, Integer}`
  (Integer enters via cross-category Eq rule referencing Int)

Overlap analysis: `Int` n `Bool` = {Ident, LParen} are ambiguous tokens.
`Integer` is unique to Int; `KwTrue`, `KwFalse` are unique to Bool.

**Generate Phase -- WFST Prediction (always-on).** The pipeline constructs
prediction WFSTs from FIRST sets and dispatch action tables. Composed
dispatch resolves ambiguous multi-accept DFA states via tropical
shortest-path composition. The pipeline emits static CSR arrays
(`PREDICTION_<CAT>_STATES`, `PREDICTION_<CAT>_ARCS`) and reorders
dispatch match arms by WFST prediction weights. CountingWeight
detects ambiguity; BooleanWeight detects dead rules. All WFST
computation happens at codegen time with zero runtime overhead.

**Generate Phase -- Dead-Rule Detection.** Five-tier analysis:
1. **Tier 1** (LiteralNoNativeType): literal rules in categories without `native_type`
2. **Tier 2** (UnreachableCategory): infix/var rules in unreachable categories
3. **Tier 3** (WfstUnreachable): prefix rules with no WFST dispatch path
4. **Tier 4** (SemanticLiveness): transitive closure over dependency groups
5. **Tier 5** (WpdsStackAware): WPDS poststar(BooleanWeight) stack-aware unreachability (W13)

**Generate Phase -- Lint Layer.** Lint diagnostics across 7 categories run against
the grammar: grammar structure (G), WFST-specific (W), recovery (R), cross-category
(C), decision tree/WPDS (D/COMP), performance (P). Output follows Rust compiler
diagnostic style to stderr.

**Generate Phase -- Trampolined Parsers.**
- `parse_Int`: Explicit continuation stack with `Frame_Int` variants.
  Prefix: `Integer(_)` -> `NumLit`, `Ident(_)` -> `IVar`,
  `LParen` -> grouped expression.
  Infix loop: `infix_bp(Token::Plus) -> Some((2, 3))`,
  `make_infix(Token::Plus, lhs, rhs) -> Int::Add(Box::new(lhs), Box::new(rhs))`.
- `parse_Bool`: No same-category infix, so infix loop exits immediately.
  Prefix: `Boolean(_)` -> `BoolLit`, `Ident(_)` -> `BVar`, `LParen` -> grouped.

**Generate Phase -- Cross-Category Dispatch.** `Eq` is a cross-category rule
(`Int "==" Int -> Bool`). The dispatch wrapper for `parse_Bool`:
- On `Integer` (unique to Int): deterministic cross-category path.
  Parse Int, expect `==`, parse Int, construct `Eq`.
- On `Ident` (ambiguous): save position, try cross-category parse
  (parse Int, check for `==`). If `==` found, commit. Otherwise,
  backtrack and try own-category (Bool) parse.
- On `KwTrue`/`KwFalse` (unique to Bool): fall through to `parse_Bool_own`.

**Finalize Phase.** Lexer code and parser code strings are concatenated and
parsed into a single `TokenStream`. Returned to the macros crate, which
injects it into the caller's module scope alongside AST, Ascent, and
Language trait implementation code.

## 7. Language Composition Entry Points

PraTTaIL supports three macro-level entry points for language definition
and composition, plus three composition clauses within `language!`.

### `language!` Macro

The primary entry point. Defines a complete language with types, terms,
equations, rewrites, and logic:

```rust
language! {
    name: Calculator,
    extends: [BaseArith],           // additive inheritance (no overrides)
    includes: [ExtraOps],           // override inheritance
    mixins: [ArithOps, BoolOps],    // fragment mixing
    types { ... },
    terms { ... },
    equations { ... },
    logic { ... },
}
```

**Composition clauses** within `language!`:

| Clause      | Strategy                      | Source                           | Duplicate Handling            |
|-------------|-------------------------------|----------------------------------|-------------------------------|
| `extends:`  | `DuplicateStrategy::Error`    | Other `language!` definitions    | Reject duplicate labels       |
| `includes:` | `DuplicateStrategy::Override` | Other `language!` definitions    | Extension label replaces base |
| `mixins:`   | `DuplicateStrategy::Override` | `language_fragment!` definitions | Fragment label replaces base  |

Resolution order: `apply_extends()` -> `apply_includes()` -> `apply_mixins()`.
All three call `merge_language_defs(base, extension, strategy)` at the
raw `LanguageDef` AST level (before validation, classification, FIRST/FOLLOW
computation, WFST construction, or optimization). The full pipeline runs
exactly once on the merged result.

Merge strategy per component:

| Component     | Strategy                                                                     |
|---------------|------------------------------------------------------------------------------|
| **types**     | Union by name; `native_type` must match if both present                      |
| **terms**     | `Error`: concatenate, reject same label. `Override`: extension replaces base |
| **equations** | Same as terms (keyed by equation name)                                       |
| **rewrites**  | Same as terms (keyed by rewrite name)                                        |
| **logic**     | Relations: union by name, error if param types differ. Content: concatenate  |
| **options**   | Extension values override base for matching keys                             |

### `language_fragment!` Macro

Defines a reusable grammar fragment (types + terms only, no equations,
rewrites, or logic). Fragments are stored in an in-process registry and
generate no code themselves -- the consuming `language!` generates everything:

```rust
language_fragment! {
    name: ArithOps,
    types { ![i32] as Int },
    terms {
        NumLit . |- Integer : Int;
        Add . a:Int, b:Int |- a "+" b : Int ![ a + b ] fold;
    }
}
```

### `compose_languages!` Macro

Composes independently defined languages into a single unified language
via runtime delegation. Unlike `extends`/`includes`/`mixins` (which merge
at the AST level), `compose_languages!` generates a thin wrapper that
delegates parsing, evaluation, and environment operations to constituent
sub-languages:

```rust
compose_languages! {
    name: Combined,
    languages: [calculator::Calculator, rhocalc::RhoCalc],
}
```

Generated code (from `compose_gen.rs`):
- `{Name}TermInner` enum -- one variant per sub-language
- `{Name}Term` wrapper struct implementing `mettail_runtime::Term`
- Downcast accessors: `as_{sub}() -> Option<&{Sub}Term>`
- `{Name}Env` struct with per-sub-language environments
- `{Name}Metadata` composed metadata aggregating sub-language metadata
- `{Name}Language` struct implementing `mettail_runtime::Language`

Delegation parsing tries each sub-language in declaration order and returns
the first success.

> **Cross-references:**
> - [design/composed-dispatch.md](composed-dispatch.md) -- WFST-composed dispatch table computation
> - [design/multi-accept-dfa.md](multi-accept-dfa.md) -- Multi-accept DFA analysis
> - [design/lazy-trampoline-parser.md](lazy-trampoline-parser.md) -- Trampoline parser architecture
> - [design/lint-layer.md](lint-layer.md) -- Lint diagnostic layer design
> - [design/prediction-engine.md](prediction-engine.md) -- FIRST/FOLLOW sets and dispatch tables
> - [design/wfst/dead-rule-detection.md](wfst/dead-rule-detection.md) -- Five-tier dead-rule detection
> - [design/wfst/wpds-analysis.md](wfst/wpds-analysis.md) -- WPDS analysis layer
> - [design/wfst/grammar-composition.md](wfst/grammar-composition.md) -- WFST grammar composition
> - [theory/wfst/semirings.md](../theory/wfst/semirings.md) -- Semiring theory
> - [design/wfst/error-recovery.md](wfst/error-recovery.md) -- WFST-weighted error recovery
