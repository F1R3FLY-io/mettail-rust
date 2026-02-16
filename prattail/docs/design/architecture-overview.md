# PraTTaIL: Architecture Overview

**Date:** 2026-02-14

---

## Table of Contents

1. [High-Level Data Flow](#1-high-level-data-flow)
2. [Pipeline Stages](#2-pipeline-stages)
3. [Module Structure](#3-module-structure)
4. [Data Types and Interfaces](#4-data-types-and-interfaces)
5. [Code Generation Assembly](#5-code-generation-assembly)
6. [Worked Example: End-to-End Flow](#6-worked-example-end-to-end-flow)

---

## 1. High-Level Data Flow

The PraTTaIL pipeline transforms a `LanguageSpec` (the serializable
representation of a `language!` macro invocation) into a `TokenStream`
containing a complete, self-contained parser.

```
                    language! { name: Calc, types { ... }, terms { ... } }
                                        |
                                        v
                             +---------------------+
                             |    macros crate      |
                             |    (proc-macro)      |
                             |                      |
                             |  Parse DSL syntax    |
                             |  Build LanguageDef   |
                             |  Project to          |
                             |    LanguageSpec       |
                             +----------+----------+
                                        |
                                        v
                               LanguageSpec {
                                 name: "Calc",
                                 types: [CategorySpec...],
                                 rules: [RuleSpec...],
                               }
                                        |
                          +-------------+-------------+
                          |                           |
                          v                           v
               +-------------------+       +--------------------+
               | Lexer Pipeline    |       | Parser Pipeline    |
               |                   |       |                    |
               | Terminal Extract  |       | Grammar Analysis   |
               |       |           |       |       |            |
               |       v           |       |       v            |
               | Automata Pipeline |       | Prediction Engine  |
               |  NFA -> DFA ->   |       |  FIRST sets ->     |
               |  Minimize ->     |       |  Dispatch tables   |
               |  Equiv Classes   |       |       |            |
               |       |           |       |       v            |
               |       v           |       | +--+-------+--+   |
               | Lexer Codegen    |       | |BP |Pratt  |RD|   |
               |  direct-coded    |       | |Tbl|Loop   |Hd|   |
               |  or table-driven |       | |Gen|Gen    |Gn|   |
               +--------+----------+       +--+-+---+---+-++   |
                        |                     |     |     |     |
                        |                     v     v     v     |
                        |              +------+-----+-----+--+  |
                        |              | Cross-Category       |  |
                        |              | Dispatch Codegen     |  |
                        |              +----------+-----------+  |
                        |                         |              |
                        +----------+--------------+              |
                                   |                             |
                                   v                             |
                          +------------------+                   |
                          |  Assembly Phase  |<------------------+
                          |                  |
                          |  lexer_code      |
                          |  helpers         |
                          |  rd_functions    |
                          |  pratt_parsers   |
                          |  dispatch_code   |
                          |  entry_points    |
                          +--------+---------+
                                   |
                                   v
                            TokenStream
                         (Rust source code)
```

## 2. Pipeline Stages

The `generate_parser()` function in `lib.rs` orchestrates seven sequential
phases. Each phase reads from the `LanguageSpec` and/or the output of
previous phases, and produces an intermediate result or final code.

```
Phase   | Input                   | Output                  | Module
--------+-------------------------+-------------------------+------------------
   1    | LanguageSpec.rules      | LexerInput              | lexer.rs
        | LanguageSpec.types      |   (terminals, builtins) |
        |                         | (TokenStream, Stats)    | automata/*
--------+-------------------------+-------------------------+------------------
   2    | LanguageSpec.rules      | BindingPowerTable       | binding_power.rs
        |   (infix rules only)    |   (per-operator BP)     |
--------+-------------------------+-------------------------+------------------
   3    | LanguageSpec.rules      | BTreeMap<String,        | prediction.rs
        | LanguageSpec.types      |   FirstSet>             |
        |                         | BTreeMap<String,        |
        |                         |   DispatchTable>        |
        |                         | BTreeMap<(S,S),         |
        |                         |   CrossCategoryOverlap> |
--------+-------------------------+-------------------------+------------------
   4    | LanguageSpec.rules      | Vec<PrefixHandler>      | recursive.rs
        |   (non-infix, non-var,  | Vec<TokenStream>        |
        |    non-literal rules)   |   (RD functions)        |
--------+-------------------------+-------------------------+------------------
   5    | Phase 2 BP table        | Vec<TokenStream>        | pratt.rs
        | Phase 3 dispatch tables |   (per-category Pratt)  |
        | Phase 4 prefix handlers |                         |
--------+-------------------------+-------------------------+------------------
   6    | Phase 3 overlaps        | Vec<TokenStream>        | dispatch.rs
        | Phase 3 first sets      |   (cross-category code) |
        | LanguageSpec.rules      |                         |
        |   (cross/cast rules)    |                         |
--------+-------------------------+-------------------------+------------------
   7    | All phases              | TokenStream             | lib.rs
        |                         |   (final assembly)      |
--------+-------------------------+-------------------------+------------------
```

## 3. Module Structure

```
prattail/src/
  |
  +-- lib.rs                 Top-level orchestration, LanguageSpec types,
  |                          generate_parser() entry point
  |
  +-- lexer.rs               Lexer pipeline orchestration:
  |                          extract_terminals(), generate_lexer()
  |
  +-- automata/
  |     +-- mod.rs           Core types: StateId, ClassId, NfaState,
  |     |                    DfaState, Nfa, Dfa, CharClass, TokenKind,
  |     |                    TerminalPattern, NfaFragment
  |     |
  |     +-- nfa.rs           Thompson's construction: build_nfa(),
  |     |                    build_string_fragment(), build_ident_fragment(),
  |     |                    build_integer_fragment(), etc.
  |     |                    Epsilon closure computation.
  |     |
  |     +-- partition.rs     Alphabet equivalence class computation:
  |     |                    compute_equivalence_classes(), AlphabetPartition
  |     |
  |     +-- subset.rs        Subset construction (NFA -> DFA):
  |     |                    subset_construction(), dfa_transition()
  |     |
  |     +-- minimize.rs      Hopcroft's DFA minimization:
  |     |                    minimize_dfa()
  |     |
  |     +-- codegen.rs       Lexer code generation:
  |                          generate_lexer_code(), Token enum generation,
  |                          direct-coded vs table-driven selection,
  |                          terminal_to_variant_name()
  |
  +-- prediction.rs          FIRST set computation (fixed-point iteration),
  |                          dispatch table construction,
  |                          cross-category overlap analysis
  |
  +-- binding_power.rs       Binding power table construction,
  |                          infix_bp / make_infix code generation
  |
  +-- pratt.rs               Pratt parser code generation per category:
  |                          main Pratt loop, prefix handler dispatch,
  |                          parse entry points, helper functions
  |
  +-- recursive.rs           Recursive descent handler generation:
  |                          per-rule parse functions for structural
  |                          constructs (binders, collections, patterns)
  |
  +-- dispatch.rs            Cross-category dispatch generation:
  |                          cast rules, comparison rules,
  |                          FIRST-set-driven backtracking decisions
  |
  +-- tests/
        +-- mod.rs
        +-- automata_tests.rs
        +-- lexer_tests.rs
        +-- prediction_tests.rs
        +-- integration_tests.rs
```

## 4. Data Types and Interfaces

### Input Types (from macros crate)

```
LanguageSpec
  +-- name: String                       "Calculator"
  +-- types: Vec<CategorySpec>
  |     +-- name: String                 "Int", "Bool", "Str"
  |     +-- native_type: Option<String>  Some("i32"), Some("bool"), ...
  |     +-- is_primary: bool             true (first), false (rest)
  +-- rules: Vec<RuleSpec>
        +-- label: String                "Add", "Eq", "PZero"
        +-- category: String             "Int", "Bool", "Proc"
        +-- syntax: Vec<SyntaxItemSpec>
        |     Terminal(String)            "+", "{}", "error"
        |     NonTerminal { category, param_name }
        |     IdentCapture { param_name }
        |     Binder { param_name, category }
        |     Collection { param_name, element_category, separator, kind }
        +-- is_infix: bool
        +-- associativity: Associativity
        +-- is_var, is_literal, is_cast, is_cross_category, ...
        +-- has_binder, has_multi_binder, is_collection, ...
        +-- rust_code: Option<TokenStream>
        +-- eval_mode: Option<String>
```

### Key Intermediate Types

```
LexerInput                               Terminal extraction result
  +-- terminals: Vec<TerminalPattern>
  +-- needs: BuiltinNeeds

BindingPowerTable                        Per-operator binding powers
  +-- operators: Vec<InfixOperator>
        +-- terminal, category, label
        +-- left_bp, right_bp

FirstSet                                 Set of token variant names
  +-- tokens: BTreeSet<String>

DispatchTable                            Per-category parse dispatch
  +-- entries: BTreeMap<String, DispatchAction>
  +-- default_action: Option<DispatchAction>

CrossCategoryOverlap                     FIRST set overlap analysis
  +-- ambiguous_tokens: FirstSet
  +-- unique_to_a, unique_to_b: FirstSet

PrefixHandler                            Per-rule prefix match arm
  +-- category, label: String
  +-- match_arm: TokenStream
```

## 5. Code Generation Assembly

Phase 7 assembles all generated code into a single `TokenStream`:

```
quote! {
    // ---- Lexer ----
    //   Token enum (Eof, Ident, Integer, Plus, Star, ...)
    //   Span struct
    //   CHAR_CLASS equivalence class table
    //   lex() function
    //   dfa_next() / TRANSITIONS table
    //   accept_token() match

    #lexer_code

    // ---- Parser Helpers ----
    //   expect_token()
    //   expect_ident()
    //   peek_token()
    //   peek_ahead()

    #helpers

    // ---- Recursive Descent Handlers ----
    //   parse_pzero()
    //   parse_pdrop()
    //   parse_ppar()
    //   parse_pinputs()
    //   ... one function per structural rule

    #(#rd_functions)*

    // ---- Pratt Parsers (per category) ----
    //   For each category C:
    //     infix_bp() match (if C has infix ops)
    //     make_infix() match (if C has infix ops)
    //     parse_C() Pratt loop
    //     parse_C_prefix() dispatch

    #(#pratt_parsers)*

    // ---- Cross-Category Dispatch ----
    //   parse_Bool() wrapper with cross-category logic
    //   (overrides the Pratt parse_Bool for categories
    //    that have cross-category or cast rules)

    #(#dispatch_code)*

    // ---- Entry Points ----
    //   impl Int  { pub fn parse(input: &str) -> Result<Int, String> }
    //   impl Bool { pub fn parse(input: &str) -> Result<Bool, String> }
    //   impl Str  { pub fn parse(input: &str) -> Result<Str, String> }

    #entry_points
}
```

## 6. Worked Example: End-to-End Flow

Consider a minimal Calculator with `Int` (i32), `Bool` (bool), and rules
`Add`, `Eq`, `NumLit`, `BoolLit`, `IVar`, `BVar`.

**Phase 1: Terminal Extraction.** Scans rules for terminal strings:
`+`, `==`. Detects native types: `i32` -> needs integer, `bool` -> needs
boolean (adds `true`/`false` keywords). Builds NFA, DFA, minimizes,
generates lexer with Token enum: `{Eof, Ident, Integer, Boolean, Plus, EqEq}`.

**Phase 2: Binding Powers.** `Add` is infix in `Int`:
`+` gets `(left_bp=2, right_bp=3)` (left-associative).

**Phase 3: Prediction.** Computes FIRST sets:
- `FIRST(Int) = {Ident, Integer, LParen}`
- `FIRST(Bool) = {Ident, KwTrue, KwFalse, LParen, Integer}`
  (Integer enters via cross-category Eq rule referencing Int)

Overlap analysis: `Int /\ Bool = {Ident, LParen}` are ambiguous tokens.
`Integer` is unique to Int; `KwTrue`, `KwFalse` are unique to Bool.

**Phase 4: RD Handlers.** No structural rules in this example (all rules
are infix, literal, variable, or cross-category).

**Phase 5: Pratt Parsers.**
- `parse_Int`: Pratt loop with `infix_bp(Token::Plus) -> Some((2, 3))`,
  `make_infix(Token::Plus, lhs, rhs) -> Int::Add(Box::new(lhs), Box::new(rhs))`.
  Prefix handler: `Integer(_)` -> `NumLit`, `Ident(_)` -> `IVar`,
  `LParen` -> grouped expression.
- `parse_Bool`: No same-category infix, so `parse_Bool` delegates to
  `parse_Bool_prefix`. Prefix: `Boolean(_)` -> `BoolLit`,
  `Ident(_)` -> `BVar`, `LParen` -> grouped.

**Phase 6: Cross-Category Dispatch.** `Eq` is a cross-category rule
(`Int "==" Int -> Bool`). The dispatch wrapper for `parse_Bool`:
- On `Integer` (unique to Int): deterministic cross-category path.
  Parse Int, expect `==`, parse Int, construct `Eq`.
- On `Ident` (ambiguous): save position, try cross-category parse
  (parse Int, check for `==`). If `==` found, commit. Otherwise,
  backtrack and try own-category (Bool) parse.
- On `KwTrue`/`KwFalse` (unique to Bool): fall through to `parse_Bool_own`.

**Phase 7: Assembly.** All code is concatenated into a single `TokenStream`
and returned to the macros crate, which injects it into the caller's module
scope.
