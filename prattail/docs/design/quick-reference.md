# PraTTaIL Internals Reference

**A comprehensive guide to PraTTaIL's contributions to MeTTaIL.**

PraTTaIL is the compile-time parser generation engine at the heart of MeTTaIL.
It transforms declarative grammar specifications into optimized Rust lexers
and parsers via a multi-phase pipeline grounded in weighted automata theory.
This document provides a scannable, diagram-rich overview of every major
subsystem: lexer construction, Pratt parsing, semiring algebra, weighted
pushdown systems, error recovery, and the advanced automata infrastructure.

---

## Reading Guide

| Audience               | Recommended Path                                                                                                                                                                                            |
|------------------------|-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| **Language designer**  | [1. Architecture](#1-system-architecture) → [2. Lexer](#2-the-lexer-pipeline) → [3. Parser](#3-the-parsing-engine) → [9. Integration](#9-integration-how-it-all-fits-together)                              |
| **Parser implementor** | [2. Lexer](#2-the-lexer-pipeline) → [3. Parser](#3-the-parsing-engine) → [5. Weighted Automata](#5-weighted-automata-layers) → [6. Optimization](#6-analysis-and-optimization)                              |
| **Automata theorist**  | [4. Semirings](#4-semiring-framework) → [5. Weighted Automata](#5-weighted-automata-layers) → [7. Advanced Automata](#7-advanced-automata-infrastructure) → [8. Analysis](#8-mathematical-analysis-modules) |
| **Contributor**        | [1. Architecture](#1-system-architecture) → [Appendix B](#b-feature-flag-reference) → [Appendix C](#c-lint-code-directory) → [6. Optimization](#6-analysis-and-optimization)                                |

### Notation Conventions

| Symbol           | Meaning                                          |
|------------------|--------------------------------------------------|
| (K, ⊕, ⊗, 0̄, 1̄)  | Semiring with plus, times, zero, one             |
| ε                | Empty string / epsilon transition                |
| Σ, Γ             | Input alphabet, stack alphabet                   |
| ⟨p, γ⟩ ↪ ⟨p', u⟩ | WPDS rule: control p, stack top γ, replacement u |
| FIRST(A)         | Set of tokens that can begin category A          |
| FOLLOW(A)        | Set of tokens that can follow category A         |
| ─, │, ┌, └, ├, ┤ | Diagram box-drawing                              |
| →, ⇒             | Data flow, implication                           |
| ✓ / ✗            | Supported / not supported                        |

---

## Table of Contents

1. [System Architecture](#1-system-architecture)
2. [The Lexer Pipeline](#2-the-lexer-pipeline)
3. [The Parsing Engine](#3-the-parsing-engine)
4. [Semiring Framework](#4-semiring-framework)
5. [Weighted Automata Layers](#5-weighted-automata-layers)
6. [Analysis and Optimization](#6-analysis-and-optimization)
7. [Advanced Automata Infrastructure](#7-advanced-automata-infrastructure)
8. [Mathematical Analysis Modules](#8-mathematical-analysis-modules)
9. [Integration: How It All Fits Together](#9-integration-how-it-all-fits-together)
- [Appendix A: Complete Semiring Quick-Reference](#a-complete-semiring-quick-reference)
- [Appendix B: Feature Flag Reference](#b-feature-flag-reference)
- [Appendix C: Lint Code Directory](#c-lint-code-directory)
- [Appendix D: Glossary](#d-glossary)
- [Appendix E: References](#e-references)

---

## 1. System Architecture

### 1.1 Workspace Layout

MeTTaIL is organized as a Cargo workspace with seven crates.  PraTTaIL
(`prattail`) provides the compile-time engine; `macros` bridges the user-facing
`language!` DSL to PraTTaIL's pipeline; `languages` houses concrete grammars;
`runtime` supplies shared runtime types; `repl` provides the interactive
evaluator; `query` adds a query language; and `ascent_syntax_export` exposes
parsed Ascent syntax for tooling.

```
┌────────────────────────────────────────────────────────────────────┐
│                        mettail-rust workspace                      │
├────────────────────────────────────────────────────────────────────┤
│                                                                    │
│  ┌──────────┐    ┌──────────┐    ┌──────────────────────────────┐  │
│  │  macros  │───→│ prattail │───→│       (generated code)       │  │
│  │          │    │          │    │  Token enum, lexer, parser,  │  │
│  │ language!│    │ pipeline │    │  Ascent Datalog program      │  │
│  │ DSL parse│    │ codegen  │    └──────────────────────────────┘  │
│  └────┬─────┘    └────┬─────┘                                      │
│       │               │                                            │
│       │    ┌──────────┘                                            │
│       │    │                                                       │
│  ┌────▼────▼──┐  ┌──────────┐  ┌──────────┐  ┌──────────────────┐  │
│  │ languages  │  │ runtime  │  │   repl   │  │ascent_syntax_    │  │
│  │            │  │          │  │          │  │  export          │  │
│  │ Calculator │  │ bindings │  │ REPL +   │  │                  │  │
│  │ Lambda     │  │ hash-cons│  │ registry │  │ build.rs parse   │  │
│  │ RhoCalc    │  │ metadata │  │ pretty   │  │                  │  │
│  │ Ambient    │  │          │  │          │  │                  │  │
│  └────────────┘  └──────────┘  └──────────┘  └──────────────────┘  │
│                                                                    │
│  ┌──────────┐                                                      │
│  │  query   │                                                      │
│  │          │                                                      │
│  │ SQL-like │                                                      │
│  │ queries  │                                                      │
│  └──────────┘                                                      │
│                                                                    │
└────────────────────────────────────────────────────────────────────┘
```

**Dependency arrows**: `macros` depends on `prattail` and `runtime`.
`languages` depends on `macros` and `runtime`.  `repl` depends on `languages`
and `runtime`.

### 1.2 End-to-End Data Flow

The journey from a `language! { ... }` invocation to executable Rust code:

```
language! { name: Calc, types { ... }, terms { ... }, ... }
          │
          ▼
    ┌───────────────┐
    │ macros/lib.rs │  parse_macro_input! → LanguageDef
    │               │  apply_extends/includes/mixins
    │               │  validate_language
    └──────┬────────┘
           │ language_def_to_spec()
           ▼
    ┌──────────────┐
    │ LanguageSpec │  categories, rules, beam_width, recovery_config,
    │              │  semantic_dependency_groups, literal_patterns
    └──────┬───────┘
           │ run_pipeline_with_analysis()
           ▼
    ┌───────────────────────────────────────────────────────────┐
    │                    PraTTaIL Pipeline                      │
    │  ┌─────────┐   ┌──────────────┐   ┌────────────────────┐  │
    │  │ Extract │──→│   Generate   │──→│     Finalize       │  │
    │  │         │   │              │   │                    │  │
    │  │ Lexer   │   │ Lexer code   │   │ Concatenate        │  │
    │  │ Bundle  │   │ Parser code  │   │ str::parse::<      │  │
    │  │         │   │ Analysis     │   │   TokenStream>()   │  │
    │  │ Parser  │   │ Lints        │   │                    │  │
    │  │ Bundle  │   │              │   │                    │  │
    │  └─────────┘   └──────────────┘   └────────────────────┘  │
    └──────────────────────┬────────────────────────────────────┘
                           │
              ┌────────────┴────────────┐
              ▼                         ▼
    ┌──────────────────┐    ┌────────────────────┐
    │  TokenStream     │    │ PipelineAnalysis   │
    │ (generated Rust) │    │ dead_rule_labels   │
    │                  │    │ constructor_weights│
    │ Token enum       │    │ decision_trees     │
    │ lex()            │    │ category_weights   │
    │ parse_<Cat>()    │    │ isomorphic_groups  │
    │ recovery helpers │    │ (feature-gated     │
    └─────────┬────────┘    │  analysis results) │
              │             └───────────┬────────┘
              │                         │
              ▼                         ▼
    ┌───────────────────────────────────────────┐
    │ macros: generate_ascent_source()          │
    │   PipelineAnalysis feeds DCE (dead-code   │
    │   elimination), rule order,               │
    │   template instantiation, demand analysis │
    └─────────┬─────────────────────────────────┘
              │
              ▼
    ┌───────────────────┐
    │ Final TokenStream │  AST types + lexer + parser +
    │                   │  Ascent Datalog program +
    │                   │  metadata + language impl
    └───────────────────┘
```

### 1.3 Annotated DSL Example

A trimmed Calculator grammar showing the key DSL constructs:

```rust
language! {
    name: Calculator,

    types {
        ![i32] as Int       // Category with native Rust type
        ![f64] as Float
        ![bool] as Bool
    }

    terms {
        // Infix operators (left-associative by default)
        AddInt . a:Int, b:Int |- a "+" b : Int ![a + b] fold;
        MulInt . a:Int, b:Int |- a "*" b : Int ![a * b] fold;

        // Right-associative exponentiation
        PowInt . a:Int, b:Int |- a "^" b : Int ![a.pow(b as u32)] step right;

        // Ternary (N-ary mixfix)
        Tern . c:Int, t:Int, e:Int |- c "?" t ":" e : Int
            ![if c != 0 { t } else { e }] step right;

        // Unary prefix
        Neg . a:Int |- "-" a : Int ![(-a)] fold;

        // Cross-category cast
        IntToFloat . a:Int |- "float" "(" a ")" : Float
            ![CanonicalFloat64::from(a as f64)] step;

        // Comparison (produces Bool)
        GtInt . a:Int, b:Int |- a ">" b : Bool ![a > b] step;
    }

    // Custom token definitions (optional, between types and terms)
    tokens {
        // Override built-in integer to support hex prefix
        Integer = /[0-9]+/ ![text.parse::<i64>().expect("bad int")];

        // New token kind: hex literals
        HexLiteral = /0x[0-9a-fA-F]+/ : Int
            ![i64::from_str_radix(&text[2..], 16).expect("bad hex")];

        // Explicit priority for disambiguation
        BinaryLiteral = /0b[01]+/ : Int
            ![i64::from_str_radix(&text[2..], 2).expect("bad bin")]
            priority(4);

        // String interpolation via modal lexing
        StringStart = /"/ push(string_body);
        mode string_body {
            StringChars = /[^"\\$]+/;
            StringEscape = /\\./;
            InterpStart = /\$\{/ push(default);
            StringEnd = /"/ pop : Str ![process_string(text)];
        }

        // Route comments to auxiliary stream
        LineComment = /\/\/[^\n]*/ -> comments;

        // Cross-stream sync constraints
        sync {
            align(comments, main) on /\n/;
            track(whitespace, main);
        }

        // Tree structural invariants (feature = "parity-tree-automata")
        tree_invariants {
            no_nested_braces: forall children of Brace { not Brace };
            no_empty_parens: forall Paren { exists child };
        }
    },

    equations { }

    rewrites {
        // Congruence rules (structural rewriting under any context)
        AddIntCongL . | S ~> T |- (AddInt S R) ~> (AddInt T R);
        AddIntCongR . | S ~> T |- (AddInt L S) ~> (AddInt L T);
    }
}
```

> **See also**: [tokens/ design docs](tokens/README.md) for detailed documentation
> of each `tokens { ... }` sub-feature.

#### `tokens { ... }` Block Grammar

```
tokens_block     ::= "tokens" "{" token_item* "}"
token_item       ::= token_def | mode_def | sync_block | invariants_block
token_def        ::= Name "=" "/" regex "/" [":" Category]
                      ["!" "[" rust_code "]"] ["priority" "(" integer ")"]
                      ["push" "(" mode_name ")"] ["pop"]
                      ["->" stream_name] ";"
mode_def         ::= "mode" Name "{" token_def* "}"
sync_block       ::= "sync" "{" sync_constraint* "}"
sync_constraint  ::= "align" "(" stream "," stream ")" "on" "/" regex "/" ";"
                    | "track" "(" stream "," stream ")" ";"
invariants_block ::= "tree_invariants" "{" invariant* "}"
invariant        ::= Name ":" constraint_expr ";"
```

| Sub-feature        | Feature Gate               | Key Functions                                  |
|--------------------|----------------------------|------------------------------------------------|
| Custom tokens      | (always on)                | `build_nfa_with_custom()`, `write_token_enum()` |
| Modal lexing       | (always on)                | `build_nfa_for_mode()`, `generate_modal_lexer_string()` |
| Multi-stream       | (always on)                | `write_stream_tables()`, `write_modal_lex_with_streams()` |
| VPA delimiter      | `vpa`                      | `build_vpa_alphabet_from_modes()`, `build_skip_table()` |
| Tree automata      | `tree-automata` + `vpa`    | `validate_token_tree()`, `token_tree_to_term()` |
| Tree invariants    | `parity-tree-automata`     | `tree_invariants { ... }` DSL                   |
| Multi-tape sync    | `multi-tape`               | `build_synced_stream_automaton()`, `sync { ... }` |

### 1.4 PraTTaIL Module Map

PraTTaIL contains 50+ modules organized by function:

**Core Parser Infrastructure** (always compiled):

| Module             | Lines  | Purpose                                                            |
|--------------------|--------|--------------------------------------------------------------------|
| `automata/`        | ~2,900 | NFA/DFA types, Thompson construction, partition, minimize, codegen |
| `automata/utf8.rs` | ~430   | UTF-8 byte chain decomposition (Unicode → byte-level NFA chains)  |
| `binding_power.rs` | ~400   | BP analysis for infix/prefix/postfix/mixfix                        |
| `classify.rs`      | ~200   | Rule type classification                                           |
| `decision_tree.rs` | ~6,800 | PathMap trie dispatch (unified mechanism)                          |
| `dispatch.rs`      | ~300   | Cross-category and cast rule dispatch generation                   |
| `ebnf.rs`          | ~200   | EBNF grammar dump                                                  |
| `lexer.rs`         | ~600   | Lexer codegen orchestrator                                         |
| `pipeline.rs`      | ~3,500 | Pipeline state machine (extract → generate → finalize)             |
| `pratt.rs`         | ~2,100 | Pratt expression parser generation                                 |
| `prediction.rs`    | ~3,300 | FIRST/FOLLOW sets, dispatch tables                                 |
| `recursive.rs`     | ~400   | Recursive descent handler generation                               |
| `token_id.rs`      | ~200   | Token enumeration and ID mapping                                   |
| `trampoline.rs`    | ~5,800 | Stack-safe continuation-passing parser                             |

**Weighted Analysis** (always compiled):

| Module                 | Lines    | Purpose                                         |
|------------------------|----------|-------------------------------------------------|
| `automata/semiring.rs` | ~5,700   | 16 semiring types, trait hierarchy, matrix_star |
| `compose.rs`           | ~400     | Language composition                            |
| `cost_benefit.rs`      | ~1,500   | 63 optimization gates, grammar profiling        |
| `decision_tree.rs`     | (shared) | Lattice algebra for dispatch actions            |
| `lattice.rs`           | ~500     | Token lattice, Viterbi decoding                 |
| `lint.rs`              | ~8,200   | 60+ diagnostics, grouping, ANSI output          |
| `recovery.rs`          | ~1,200   | Error recovery (5 tiers, 6 repair actions)      |
| `tensor.rs`            | ~300     | Tensor product semiring                         |
| `wfst.rs`              | ~2,500   | Prediction WFST construction and queries        |
| `wpds.rs`              | ~3,200   | Weighted pushdown systems                       |

**Mathematical Analysis** (always compiled):

| Module                | Lines | Purpose                            |
|-----------------------|-------|------------------------------------|
| `algebraic.rs`        | ~400  | Tarjan path expressions            |
| `cegar.rs`            | ~300  | CEGAR loop                         |
| `forward_backward.rs` | ~400  | Forward-backward scoring           |
| `newton.rs`           | ~300  | Newton's method fixpoint           |
| `repair.rs`           | ~500  | Analysis-driven repair suggestions |
| `verify.rs`           | ~400  | Safety/liveness verification       |

**Feature-Gated Analysis** (29 modules across 24 independent + 5 composite
features).  See [Appendix B](#b-feature-flag-reference) for the complete
feature → module → file mapping.

**Utility and Infrastructure:**

| Module                    | Gate              | Purpose                                                                                            |
|---------------------------|-------------------|----------------------------------------------------------------------------------------------------|
| `runtime_types.rs`        | core              | Shared runtime types (`Position`, `Range`, `ParseError`), generic lex loops                        |
| `prefix_trie.rs`          | core              | Prefix trie for grammar left-factoring (A1 optimization)                                           |
| `transducer.rs`           | core              | FST transduction primitives (`OptimizationPass` trait, `TransducerCascade`)                        |
| `composition_optimize.rs` | core              | 4-pass WFST composition optimization cascade                                                       |
| `composition_verify.rs`   | core              | WFST composition correctness verification                                                          |
| `test_generators.rs`      | `cfg(test)`       | Shared proptest grammar generators (`arb_grammar`, `arb_rule`)                                     |
| `training.rs`             | `wfst-log`        | Weight training loop (SGD (stochastic gradient descent) from corpus, `TrainedModel` serialization) |
| `log_push.rs`             | `wfst-log`        | Log-pushing: normalize WFST edge weights                                                           |
| `grammar_gen.rs`          | `grammar-gen`     | Grammar-aware expression string generator for benchmarks                                           |
| `ewpds.rs`                | `wpds-extended`   | Extended WPDS with merging functions                                                               |
| `relational.rs`           | `wpds-relational` | Relational weight domain for Boolean program analysis                                              |
| `ara.rs`                  | `wpds-ara`        | Affine-Relation Analysis (vector spaces of matrices)                                               |
| `ltl.rs`                  | `ltl`             | LTL formula parsing, Buchi compilation, `check_ltl_property()`                                     |

### 1.5 Key Types

The central data types that flow through the pipeline:

**LanguageSpec** — the pipeline's input:

```rust
pub struct LanguageSpec {
    pub name: String,
    pub types: Vec<CategorySpec>,
    pub rules: Vec<RuleSpec>,
    pub beam_width: BeamWidthConfig,
    pub log_semiring_model_path: Option<String>,
    pub literal_patterns: LiteralPatterns,
    pub recovery_config: RecoveryConfig,
    pub semantic_dependency_groups: Vec<HashSet<String>>,
}
```

**CategorySpec** — a syntactic sort:

```rust
pub struct CategorySpec {
    pub name: String,                    // e.g., "Int", "Bool"
    pub native_type: Option<String>,     // e.g., "i32", "bool"
    pub is_primary: bool,                // first category = primary
}
```

**RuleSpec** — a grammar rule (fully classified):

```rust
pub struct RuleSpec {
    pub label: String,                   // e.g., "AddInt"
    pub category: String,               // e.g., "Int"
    pub syntax: Vec<SyntaxItemSpec>,     // the rule's syntax items
    pub is_infix: bool,
    pub associativity: Associativity,    // Left | Right
    pub is_var: bool,
    pub is_literal: bool,
    pub is_unary_prefix: bool,
    pub is_postfix: bool,
    pub is_collection: bool,
    pub is_cross_category: bool,
    pub is_cast: bool,
    pub has_binder: bool,
    pub has_rust_code: bool,
    pub rust_code: Option<TokenStream>,
    pub eval_mode: Option<String>,       // "fold" | "step"
    pub source_location: Option<SourceLocation>,
    // ... additional fields
}
```

**SyntaxItemSpec** — elements of a rule's syntax:

```rust
pub enum SyntaxItemSpec {
    Terminal(String),                    // keyword or operator: "+", "if"
    NonTerminal { category, param_name },  // e.g., a:Int
    IdentCapture { param_name },         // identifier capture
    Binder { param_name, category, is_multi },  // ^x.body
    Collection { param_name, element_category, separator, kind },
    Sep { body, separator, kind },       // separated list
    Map { body_items },                  // structure mapping
    Zip { left_name, right_name, left_category, right_category, body },
    Optional { inner },                  // optional group
}
```

### 1.5 Feature Gate Groupings

PraTTaIL modules are organized into progressively broader feature sets:

```
core (always on)
  │  automata, pipeline, pratt, prediction, trampoline,
  │  decision_tree, wfst, wpds, recovery, lint, cost_benefit,
  │  lexer, lattice, compose, algebraic, newton, forward_backward,
  │  verify, cegar, repair, tensor, ...
  │
  ├─ wfst-log
  │    LogWeight, EntropyWeight, training, log_push, n_best_paths
  │
  ├─ analysis (tree-automata + vpa + trs-analysis)
  │
  ├─ verification (omega + ltl + kat + wpds-relational)
  │
  ├─ process-algebra (nominal + petri + omega + alternating +
  │                    symbolic-automata + two-way-transducer)
  │
  ├─ predicated-types (symbolic-automata + weighted-mso +
  │                     parity-tree-automata + register-automata +
  │                     multi-tape + multiset-automata + two-way-transducer)
  │
  └─ full-analysis (ALL feature flags)
```

See [Appendix B](#b-feature-flag-reference) for the complete feature flag
dependency graph.

---

## 2. The Lexer Pipeline

PraTTaIL generates DFA-based lexers from grammar terminal declarations.
The pipeline follows the classical Thompson–Rabin-Scott–Hopcroft chain,
enhanced with Aho-Corasick keyword tries and equivalence class compression.

### 2.1 Pipeline Overview

```
Terminals from grammar
        │
        ▼
┌───────────────────┐
│ Thompson NFA      │  Fragment composition:
│                   │  concat ─── s₁ ──ε──→ s₂
│ build_nfa()       │  alt    ─── ε──→ s₁  ε──→ accept
│                   │             ε──→ s₂  ε──→ accept
│ + Aho-Corasick    │  star   ─── ε──→ body ──ε──→ accept
│   keyword trie    │             ε──────────────→ accept
└────────┬──────────┘             ◄──────ε────── body
         │
         ▼
┌───────────────────┐
│ Equivalence Class │  Partition 256 bytes into ~15-30 classes.
│ Partition         │  Bytes triggering identical NFA transitions
│                   │  are grouped: 256 columns → ~15-30.
│ compute_equiv_    │
│   classes()       │  Compression ratio: ~10-17×
└────────┬──────────┘
         │
         ▼
┌───────────────────┐
│ Subset Construct. │  Rabin-Scott powerset construction.
│ (NFA → DFA)       │  Each DFA state = set of NFA states.
│                   │  Uses equivalence classes as alphabet.
│ subset_           │
│   construction()  │
└────────┬──────────┘
         │
         ▼
┌───────────────────┐
│ Hopcroft Minimize │  Merge equivalent DFA states.
│                   │  Typically 30-60% state reduction.
│ minimize_dfa()    │
└────────┬──────────┘
         │
         ▼
┌───────────────────┐
│ Codegen Strategy  │  Direct (≤30 states): match arms
│ Selection         │  Table (>30 states): flat array
│                   │  Hybrid (AL02): hot direct + cold table
│ analyze_sparsity()│
└────────┬──────────┘
         │
         ▼
  Generated Rust code: Token enum, lex(), lex_weighted_core()
```

### 2.2 Thompson NFA Construction

Each terminal pattern is converted to an NFA fragment using Thompson's
construction (Thompson 1968).  Fixed-string terminals (keywords, operators)
share a prefix via an Aho-Corasick trie rooted at a single epsilon
transition from the global start state, replacing per-terminal epsilon
chains.

**Fragment composition rules:**

```
Concatenation:  s₁ ──[a]──→ accept₁ ──ε──→ s₂ ──[b]──→ accept₂

Alternation:    start ──ε──→ s₁ ──[a]──→ accept₁ ──ε──→ accept
                      ──ε──→ s₂ ──[b]──→ accept₂ ──ε──→ accept

Kleene star:    start ──ε──→ body ──[a]──→ body_accept ──ε──→ accept
                      ──ε──→ accept                    ──ε──→ body
```

Built-in patterns (`ident`, `integer`, `float`, `string`) are injected
when the grammar declares native types (`i32`, `f64`, `String`, `bool`).

**Unicode patterns** (`\p{…}`, `\u{…}`, codepoint ranges in `[…]`) are
decomposed into byte-level NFA chains at compile time by
`automata/utf8.rs`. Each codepoint range is converted via
`regex_syntax::utf8::Utf8Sequences` into minimal sets of byte-range
chains (1-4 bytes per chain depending on UTF-8 encoding length). All
chains share the same start and accept states, so the NFA structure is
unchanged — only byte-range transitions are added. The downstream
pipeline (partition, subset construction, DFA minimization, codegen)
operates exclusively on the `[u8; 256]` alphabet with no modifications.

### 2.3 Equivalence Class Partition

The full 256-byte alphabet is partitioned into equivalence classes:
bytes that produce identical transitions in every NFA state are grouped
together.  This typically reduces the alphabet from 256 to 12-18 classes
(~15-20× compression), yielding proportionally smaller DFA transition tables.

### 2.4 Subset Construction

The Rabin-Scott algorithm (Rabin & Scott 1959) converts the NFA to a DFA.
Each DFA state represents a set of simultaneously-active NFA states.  The
epsilon closure is computed once per DFA state using a worklist algorithm
with O(closure_size) visited-set reset (avoiding full HashSet clear).

### 2.5 DFA Minimization

Hopcroft's algorithm (Hopcroft 1971) merges equivalent DFA states.  The
implementation uses flat byte signatures and a `HashMap` for equivalence
class computation, eliminating per-state inner `Vec` allocations.  Inverse
map pre-counting provides exact inner `Vec` capacity.

### 2.6 Codegen Strategy Selection

| Strategy      | Condition         | Description                                                      |
|---------------|-------------------|------------------------------------------------------------------|
| Direct        | ≤ 30 DFA states   | Each state is a match arm in `dfa_next()`                        |
| Table         | > 30 states       | Flat `TRANSITIONS` array with row indexing                       |
| Hybrid (AL02) | Optimization gate | Hot states (BFS depth ≤ 2) direct-coded, cold states table-based |

### 2.7 Keyword Recognition (MPH)

Fixed-string terminals (keywords) are recognized via a minimal perfect hash
(MPH) lookup after DFA acceptance.  The MPH maps keyword text to token
variant in O(1) time, avoiding sequential string comparison.

**Generated output:**
- `Token<'a>` enum with zero-copy borrowed fields (`Ident(&'a str)`,
  `StringLit(&'a str)`)
- `Position` and `Range` structs for source locations
- `ParseError` enum: `UnexpectedToken`, `UnexpectedEof`, `TrailingTokens`,
  `LexError`, `RecoveryApplied` — error messages display Unicode
  characters correctly (e.g., `unexpected character '→'`)
- `lex()` — linear tokenization returning `Vec<(Token, Range)>`
- `lex_weighted_core()` — weighted tokenization returning
  `Vec<(Token, Range, TropicalWeight)>` for lattice construction

**Pipeline statistics** (`LexerStats`):

```rust
pub struct LexerStats {
    pub num_terminals: usize,            // grammar terminals extracted
    pub num_nfa_states: usize,           // Thompson NFA states
    pub num_dfa_states: usize,           // after subset construction
    pub num_minimized_states: usize,     // after Hopcroft minimization
    pub num_equiv_classes: usize,        // alphabet partition size
    pub codegen_strategy: CodegenStrategy, // Direct | Table | Hybrid
    pub dead_fraction: f64,              // fraction of unreachable transitions
    pub variant_map: TokenVariantMap,    // token text → ordinal
    pub ambiguity_info: LexerAmbiguityInfo,
}
```

**Built-in pattern detection:** The lexer automatically recognizes native
types from category declarations and injects the corresponding patterns:

| Native Type     | Pattern                            | Injected Tokens            |
|-----------------|------------------------------------|----------------------------|
| `i32`, `i64`    | `[0-9]+`                           | `Integer`                  |
| `f64`           | `[0-9]+\.[0-9]+([eE][+-]?[0-9]+)?` | `Float`                    |
| `bool`          | —                                  | `True`, `False` (keywords) |
| `String`, `str` | `"([^"\\]\|\\.)*"`                 | `StringLit`                |

Custom literal patterns are configurable via `literal_patterns.ebnf`.

The default `<ident>` pattern is ASCII-only (`[a-zA-Z_][a-zA-Z0-9_]*`).
For Unicode identifiers, override with `\p{XID_Start}\p{XID_Continue}*`
in `literal_patterns.ebnf`. See [Section 2.8](#28-regex-pattern-syntax)
for the full regex syntax reference.

### 2.8 Regex Pattern Syntax

Token patterns are specified as PCRE-subset regular expressions compiled
directly into Thompson NFA fragments by `automata/regex.rs`. No intermediate
AST is allocated — NFA states and transitions are emitted as the pattern is
parsed.

**Feature table:**

| Feature            | Syntax                                                                     | Notes                                          |
|--------------------|----------------------------------------------------------------------------|------------------------------------------------|
| Literal char       | `a`, `1`, `_`                                                              | Single byte                                    |
| Escaped metachar   | `\.` `\\` `\[` `\]` `\(` `\)` `\|` `\+` `\*` `\?` `\^` `\"` `\{` `\}` `\/` |                                                |
| Escape sequences   | `\n` `\r` `\t`                                                             | Common whitespace                              |
| Shorthand classes  | `\d` `\w` `\s` `\D` `\W` `\S`                                              | ASCII-only (see note below)                    |
| Unicode escape     | `\u{03B1}`  `\u03B1`  `\U000003B1`                                         | Braced (1-6 hex), 4-digit, 8-digit             |
| Unicode property   | `\p{XID_Start}`  `\P{White_Space}`                                         | General categories, binary properties, scripts |
| Character class    | `[abc]`  `[a-z]`  `[α-ω]`  `[\u0391-\u03C9]`                               | Byte or codepoint ranges                       |
| Negated class      | `[^abc]`  `[^\p{Letter}]`                                                  | Complement over full byte/codepoint range      |
| Dot                | `.`                                                                        | Any byte except `\n`                           |
| Grouping           | `(...)`                                                                    | Non-capturing                                  |
| Alternation        | `a\|b`                                                                     |                                                |
| Quantifiers        | `*`  `+`  `?`                                                              | Greedy (NFA semantics)                         |
| Bounded repetition | `{n}`  `{n,}`  `{n,m}`  `{,n}`  `{,}`                                      | Count-bounded                                  |

**Not supported:** backreferences, lookahead/lookbehind, lazy quantifiers,
named groups, anchors (`^`/`$` outside character classes).

**Shorthand class note:** `\w`, `\d`, `\s` (and their negations) use ASCII
ranges for backward compatibility. For Unicode-aware matching, use `\p{…}`
explicitly: `\p{XID_Continue}` instead of `\w`, `\p{Nd}` instead of `\d`,
`\p{White_Space}` instead of `\s`.

#### Unicode support: byte-level UTF-8 automata

Multi-byte codepoints are decomposed into byte-level NFA transition chains
at compile time. The downstream pipeline (partition `[ClassId; 256]`, subset
construction, DFA minimization, codegen `[u8; 256]`, runtime lex loop) is
completely unchanged. **Zero UTF-8 decoding at lex time.**

The decomposition uses `regex_syntax::utf8::Utf8Sequences`. Example for
`α` (U+03B1, UTF-8 bytes `0xCE 0xB1`):

```
Pattern: \u{03B1}

NFA:  start ──[0xCE]──→ s₁ ──[0xB1]──→ accept

A range like [α-ω] (U+03B1–U+03C9) produces multiple byte-range chains:

      start ──[0xCE]──→ s₁ ──[0xB1-0xBF]──→ accept    (α through ...)
            ──[0xCF]──→ s₂ ──[0x80-0x89]──→ accept    (... through ω)
```

Each `Utf8Sequence` becomes a chain of 1-4 NFA transitions (one per
byte in the encoding). All chains share the same `start` and `accept`
states — the NFA structure is standard Thompson.

#### Customizable literal patterns

Default patterns are defined in `literal_patterns.ebnf`:

| Pattern     | Default Regex                        | Token       |
|-------------|--------------------------------------|-------------|
| `<integer>` | `/[0-9]+/`                           | `Integer`   |
| `<float>`   | `/[0-9]+\.[0-9]+([eE][+-]?[0-9]+)?/` | `Float`     |
| `<string>`  | `/"([^"\\]\|\\.)*"/`                 | `StringLit` |
| `<ident>`   | `/[a-zA-Z_][a-zA-Z0-9_]*/`           | `Ident`     |

The default `<ident>` pattern is ASCII-only. For Unicode identifiers,
override via `LiteralPatterns`:

```
<ident> = /\p{XID_Start}\p{XID_Continue}*/
```

This accepts identifiers like `café`, `λ`, `你好` — any codepoint with the
Unicode `XID_Start` / `XID_Continue` property.

### 2.9 Unicode Whitespace

The lex loop skips whitespace between tokens using a two-tier strategy:

1. **ASCII fast path:** `' '`, `\t`, `\n`, `\r` — the same four bytes as
   before, with optional SIMD acceleration (`simd-whitespace` feature).
2. **Unicode fallback:** After the ASCII loop, if the current byte is
   `≥ 0x80`, decode the UTF-8 character and check `char::is_whitespace()`.
   This handles NBSP (U+00A0), EN QUAD (U+2000), IDEOGRAPHIC SPACE
   (U+3000), and all other Unicode whitespace codepoints.

**Cost:** The `bytes[pos] >= 0x80` branch is never taken for pure-ASCII
input (predicted-not-taken, zero overhead). For Unicode whitespace, one
`decode_char_at()` call per whitespace character — negligible.

The fallback is applied in all three lex variants: `lex_core()`,
`lex_weighted_core()`, and `lex_lattice_core()`.

**Error display:** When the lexer encounters an unexpected character,
`decode_char_at()` decodes the full Unicode character for the error
message (e.g., `unexpected character '→'` instead of `unexpected byte
0xE2`). Caret length in `format_error_context()` uses `.chars().count()`
instead of byte count, so `café` gets 4 carets, not 5.

---

## 3. The Parsing Engine

PraTTaIL combines Pratt parsing for expression-level constructs with
recursive descent for structural constructs, unified under a trampolined
continuation-passing architecture with a PathMap-based dispatch tree.

### 3.1 Pratt Parsing

Pratt parsing (Pratt 1973) handles operator precedence and associativity
via binding power (BP) pairs.  Each infix, postfix, and mixfix operator
receives a `(left_bp, right_bp)` pair that controls parsing order.

**Core loop pseudocode:**

```
fn parse_Expr(min_bp: u8) -> Expr:
    lhs = parse_Expr_prefix()         // nud: prefix/atom
    loop:
        op = peek()
        (left_bp, right_bp) = infix_bp(op)
        if left_bp < min_bp:
            break                      // operator too weak
        advance()
        rhs = parse_Expr(right_bp)     // recursive descent at right_bp
        lhs = make_infix(op, lhs, rhs) // construct AST node
    return lhs
```

**Binding power assignment** (0-indexed level *k*, where `precedence = 2 + 2k`):

| Operator Type                | Formula                            | Example              |
|------------------------------|------------------------------------|----------------------|
| Left-assoc infix at level k  | `(2k+2, 2k+3)`                     | k=1 (`+`): `(4, 5)`  |
| Right-assoc infix at level k | `(2k+3, 2k+2)`                     | k=0 (`?:`): `(3, 2)` |
| Unary prefix                 | `(0, max_infix_bp + 2)`            | `(0, 11)`            |
| Postfix at index j           | `(max_non_postfix_bp + 4 + 2j, 0)` | j=0 (`!`): `(13, 0)` |
| Mixfix                       | Same as infix formula              | `(3, 2)`             |

#### 3.1.1 Implicit Binding Power Deduction

BP is deduced per-category from declaration order. The algorithm in
`binding_power.rs:266–333` runs in two passes:

- **Pass 1 (non-postfix):** Iterates non-postfix operators in declaration
  order. A running `precedence` counter starts at 2 (reserving 0 for entry
  and 1 for lowest-priority operands). Each operator consumes two levels
  (`precedence += 2`). Left-associative operators get `(precedence,
  precedence + 1)`; right-associative get `(precedence + 1, precedence)`.
- **Pass 2 (postfix):** Starts at `postfix_prec = precedence + 2`, leaving
  a gap of 2 above the non-postfix range for unary prefix. Each postfix
  operator gets `left_bp = postfix_prec + 1, right_bp = 0`, then
  `postfix_prec += 2`.

The formulas above (see table) follow directly from the two-pass structure.

Prefix BP is computed in `lib.rs` at code-generation time by scanning the
per-category `InfixOperator` table for the maximum BP value among
non-postfix operators and adding 2.

Cross-ref: [`binding-powers/02-implicit-deduction.md`](binding-powers/02-implicit-deduction.md)

#### 3.1.2 Explicit Binding Power Specification

Two DSL annotations are available after the evaluation mode in `language!`
rules (source: `macros/src/ast/grammar.rs:97–340`):

1. **`right`** — marks the rule as right-associative (swaps left_bp and
   right_bp in the formula above).
   ```rust
   Pow . a:Int, b:Int |- a "^" b : Int ![a.pow(b as u32)] step right;
   ```

2. **`prefix(N)`** — overrides the default prefix BP with an explicit
   value *N*, allowing different prefix operators within the same category
   to have distinct binding strengths.
   ```rust
   Neg . a:Int |- "-" a : Int prefix(5);
   ```

Both annotations can appear on the same rule in any order. When neither is
present, the operator defaults to left-associative with the implicit BP
from its declaration position.

Cross-ref: [`binding-powers/03-explicit-specification.md`](binding-powers/03-explicit-specification.md)

#### 3.1.3 Precedence–Associativity Relationship

The Pratt loop's `if left_bp < min_bp: break` comparison creates
associativity through BP asymmetry:

| BP Relationship      | Associativity | Parse of `a OP b OP c` |
|----------------------|---------------|------------------------|
| `left_bp < right_bp` | Left          | `(a OP b) OP c`        |
| `left_bp > right_bp` | Right         | `a OP (b OP c)`        |

**Mechanism:** When a second instance of the same operator appears, its
`left_bp` is compared against the parent call's `right_bp` (passed down as
`min_bp`). For left-associative `(2k+2, 2k+3)`: the second operator's
`left_bp = 2k+2` is strictly less than `min_bp = 2k+3`, so the loop breaks
and reduces — left-associative grouping. For right-associative `(2k+3,
2k+2)`: `left_bp = 2k+3 ≥ min_bp = 2k+2`, so the loop continues and
shifts — right-associative grouping.

**Floyd correspondence:** `rbp(a) < lbp(b)` ⟹ shift (b captures its left
operand); `rbp(a) > lbp(b)` ⟹ reduce (a retains its right operand).

Cross-ref: [`binding-powers/01-fundamentals.md`](binding-powers/01-fundamentals.md)

#### 3.1.4 Worked Example: CalcExample

A grammar with all operator types (from `binding-powers/05-worked-examples.md`):

```rust
language! {
    name: CalcExample,
    types { ![i32] as Int },
    terms {
        Tern . c:Int, t:Int, e:Int |- c "?" t ":" e : Int right;  // ternary
        Add  . a:Int, b:Int |- a "+" b : Int;                     // addition
        Mul  . a:Int, b:Int |- a "*" b : Int;                     // multiplication
        Pow  . a:Int, b:Int |- a "^" b : Int right;               // exponentiation
        Neg  . a:Int |- "-" a : Int;                              // negation
        Fact . a:Int |- a "!" : Int;                              // factorial
    },
}
```

**Pass 1 (non-postfix, declaration order):**

| Rule | Level *k* | Assoc | Formula        | BP Pair    |
|------|-----------|-------|----------------|------------|
| Tern | 0         | Right | (2·0+3, 2·0+2) | **(3, 2)** |
| Add  | 1         | Left  | (2·1+2, 2·1+3) | **(4, 5)** |
| Mul  | 2         | Left  | (2·2+2, 2·2+3) | **(6, 7)** |
| Pow  | 3         | Right | (2·3+3, 2·3+2) | **(9, 8)** |

After pass 1: `precedence = 2 + 2·4 = 10`, `max_infix_bp = 9`.

**Prefix:** `prefix_bp = 9 + 2 = 11` → Neg gets `(0, 11)`.

**Pass 2 (postfix):** `postfix_prec = 10 + 2 = 12` → Fact gets `left_bp = 13`.

```
 BP: 0  1  2  3  4  5  6  7  8  9  10 11 12 13
     │     │  │  │  │  │  │  │  │     │     │
     │     │ Tern│ Add │ Mul │ Pow    │     │
     │     │(R:3,2)│(L:4,5)│(L:6,7)│(R:9,8) Neg   Fact
   entry              │                  prefix postfix
  (min_bp=0)          │                  bp=11  l_bp=13
                      │
              BP number line
```

Cross-ref: [`binding-powers/05-worked-examples.md`](binding-powers/05-worked-examples.md)

**Parse tree example** for `1 + 2 * 3`:

```
         AddInt(2,3)
        ╱           ╲
   Lit(1)        MulInt(4,5)
    bp=∞        ╱           ╲
            Lit(2)        Lit(3)
             bp=∞          bp=∞

   + has bp=(2,3), * has bp=(4,5)
   At min_bp=0: parse prefix → Lit(1)
   See +, left_bp=2 ≥ 0 → consume +
   Recurse at right_bp=3: parse prefix → Lit(2)
   See *, left_bp=4 ≥ 3 → consume *
   Recurse at right_bp=5: parse prefix → Lit(3)
   See EOF, break → return MulInt
   Back to + level: MulInt returned as rhs
   See EOF, break → return AddInt
```

**Key optimizations:**

| ID   | Name                  | Description                                                          |
|------|-----------------------|----------------------------------------------------------------------|
| BP02 | Tail-call elimination | Single same-category NT in tail position → reuse frame               |
| BP03 | Static array lookup   | `static INFIX_BP_Cat: [(u8, u8); N]` when ≥ 8 operators              |
| BP05 | Bitset early-exit     | `u16` bitset guard: `if (ACTIVE_BP >> (cur_bp - LO)) == 0 { break }` |

### 3.2 Recursive Descent

Constructs that don't fit the Pratt loop — binders, collections, structural
rules with multiple nonterminal captures — are handled by generated
recursive descent handlers.  Each RD rule becomes a function
`parse_<Cat>_rd_<Label>()` that consumes tokens sequentially.

**What goes where:**

| To Pratt             | To Recursive Descent                  |
|----------------------|---------------------------------------|
| Infix operators      | Binder rules (`^x. body`)             |
| Postfix operators    | Collection rules (`[a, b, c]`)        |
| Mixfix operators     | Structural rules with ≥ 2 NT captures |
| Simple prefix + atom | Sep/Map/Zip decompositions            |

**Collection kinds:** `List`, `Set`, `Bag`, `Multiset`, with configurable
separators and optional trailing separators.

### 3.3 Trampoline Architecture

Deep nesting (e.g., 100,000 nested parentheses) would overflow the OS call
stack with naive recursion.  PraTTaIL replaces the call stack with an
explicit continuation stack (`Vec<Frame_Cat>`), enabling arbitrary depth.

**Three-phase loop:**

```
┌─────────────────────────────────────────────────────────┐
│                    'drive: loop                         │
│  ┌──────────────┐    ┌──────────────┐    ┌───────────┐  │
│  │ Parse prefix │───→│ Infix loop   │───→│ Pop frame │  │
│  ├──────────────┤    ├──────────────┤    ├───────────┤  │
│  │ nud handler  │    │ led chain:   │    │ Resume    │  │
│  │ → push frame │    │ postfix →    │    │ caller    │  │
│  │   or return  │    │ mixfix →     │    │ with lhs  │  │
│  │   value      │    │ infix →      │    │           │  │
│  │              │    │ delegation   │    │ If empty: │  │
│  │              │    │ → break      │    │ return    │  │
│  └──────────────┘    └──────────────┘    └───────────┘  │
└─────────────────────────────────────────────────────────┘
```

**Frame variants** (per-category `enum Frame_Cat`):

| Variant                  | Purpose                       | Fields                              |
|--------------------------|-------------------------------|-------------------------------------|
| `InfixRHS`               | After infix operator consumed | `lhs`, `op_pos`, `saved_bp`         |
| `UnaryPrefix_<Label>`    | After unary prefix consumed   | `saved_bp`                          |
| `RD_<Label>_N`           | After Nth capture in RD rule  | `saved_bp`, accumulated captures    |
| `CollectionElem_<Label>` | Collection element loop       | `elements`, `saved_pos`, `saved_bp` |
| `Mixfix_<Op>_N`          | Nth mixfix operand            | `lhs`, `saved_bp`, params 0..N-1    |
| `LambdaBody_Single`      | Lambda body parse             | `binder_name`, `saved_bp`           |
| `CastWrap_<Label>`       | Cross-category cast resume    | `saved_bp`                          |

**Performance:** 100K+ nesting depth (vs ~10K crash with recursion).
Overhead: -15% for nesting benchmarks, -9% for infix, -6% cross-category.

**Thread-local frame pooling:** `Cell<Vec<Frame_Cat>>` with take/set for
zero-allocation frame reuse across parse invocations.

#### 3.3.1 From Recursive Descent to Pushdown Automaton

Traditional recursive descent uses the OS call stack as an implicit pushdown
stack. The trampoline replaces this with an explicit `Vec<Frame_Cat>`,
making the parser structurally equivalent to a pushdown automaton (PDA).
All state is encoded in the stack contents and current token position,
so a single control location suffices — the `'drive`/`'unwind` loop
alternation selects the active phase.

| PDA Concept                   | Trampoline Implementation                      |
|-------------------------------|------------------------------------------------|
| Stack alphabet Γ              | `Frame_Cat` enum variants                      |
| Stack configuration ⟨p, γ⟩    | `(saved_bp, captured fields)` in each frame    |
| Push δ(p, a, γ) → (p', γ'γ)   | `stack.push(frame)` + `continue 'drive`        |
| Pop δ(p, ε, γ) → (p', ε)      | `match stack.pop()` in `'unwind`               |
| Replace δ(p, a, γ) → (p', γ') | Inline terminal consumption (no stack change)  |
| Control location p            | Single location; `'drive`/`'unwind` phase flag |
| Acceptance                    | Empty stack + successful parse result          |

The explicit stack provides two critical advantages over implicit recursion:
arbitrary nesting depth (100K+ vs ~10K) and the ability to inspect and
constrain the stack contents at compile time.

#### 3.3.2 Context-Sensitive Parsing via ContextWeight

Once the stack is explicit, it becomes possible to analyze and constrain
the set of reachable grammar rules at each point in the parse. ContextWeight
(`semiring.rs:775–903`) is a 128-bit bitset where each bit corresponds to
a grammar rule label.

During NFA disambiguation (`trampoline.rs:1145–1163`), the generated code
calls `live_rules_context_after()` on the prediction WFST, passing the
current dispatch token. This returns the ContextWeight for the current
WFST state — a bitset of rules that are reachable given the token sequence
already seen. Rules whose bits are not set are filtered out before trial
parsing:

```
  N RD candidates  →  ContextWeight filter  →  k candidates (often k = 1)
      (all rules        (WFST-informed           (reduced trial set,
       for token)        narrowing)               faster dispatch)
```

This is context-sensitive because the filter depends on the prefix of the
token stream already consumed, encoded in the WFST state — information that
a context-free lookahead cannot capture.

#### 3.3.3 From PDA to Weighted Pushdown System

The explicit stack naturally enables static analysis via weighted pushdown
systems. `build_wpds()` (`wpds.rs:388–644`) models the trampoline's stack
operations directly as WPDS rules:

| Trampoline Operation   | WPDS Rule Type | Stack Effect                                      |
|------------------------|----------------|---------------------------------------------------|
| Enter category         | Replace        | ⟨p, ⟨Cat⟩⟩ ↪ ⟨p, ⟨Cat.Rule@0⟩⟩                    |
| Cross-category NT call | Push           | Push return address, enter callee category        |
| Terminal consumption   | Replace        | Advance position within rule: @k → @(k+1)         |
| Rule completion        | Pop            | Return to caller (pop frame, resume at saved pos) |

Two saturation algorithms analyze the resulting WPDS:

- **Poststar** (`wpds.rs:707–854`): Forward reachability — computes all
  stack configurations reachable from the initial configuration, considering
  the full stack structure. Discovers which rules can actually fire.
- **Prestar** (`wpds.rs:855+`): Backward reachability — given a target
  configuration, computes which initial states can reach it. Used for
  dead-rule detection.

These enable the W13 lint (WPDS-unreachable rules) and Tier 5 dead-code
elimination, providing stronger guarantees than the NFA-only analysis
because WPDS tracks the call stack — it can detect that a rule is
unreachable due to call-chain constraints even when the NFA considers it
live.

Cross-ref: [§5.2 Weighted Pushdown System (WPDS)](#52-weighted-pushdown-system-wpds)

#### 3.3.4 The Progression

Each step in PraTTaIL's evolution was a natural consequence of the previous:

```
Recursive Descent → Trampoline → PDA           → ContextWeight      → WPDS
(implicit stack)    (explicit    (structural     (context-sensitive   (weighted
 stack-limited)      stack,       equivalence)    dispatch             reachability,
                     arbitrary                    narrowing via        dead-rule
                     depth)                       128-bit bitset)      proofs)
```

Making the stack explicit enabled analyzing it; analyzing it enabled
weighting it; weighting it enabled proving properties about grammar
reachability — from stack safety to dispatch precision to dead-code
elimination.

### 3.4 Prediction Engine

The prediction engine computes FIRST and FOLLOW sets for dispatch decisions.

**FIRST set computation** (fixed-point iteration with dirty-flag convergence):

```
FIRST(A) = ∅
repeat:
    changed = false
    for each rule A → α₁α₂...αₙ:
        for each αᵢ in α₁...αₙ:
            if αᵢ is terminal t:
                changed |= FIRST(A).insert(t)
                break
            if αᵢ is nonterminal B:
                changed |= FIRST(A) ∪= FIRST(B) \ {ε}
                if ε ∉ FIRST(B): break
            if αᵢ is ident: changed |= FIRST(A).insert(Ident); break
        if all αᵢ nullable: A.nullable = true
until !changed
```

**FOLLOW set computation:**

```
FOLLOW(primary) ∪= {Eof}
for each rule A → ...Bβ...:
    FOLLOW(B) ∪= FIRST(β) \ {ε}
    if β is nullable:
        FOLLOW(B) ∪= FOLLOW(A)
```

**DispatchAction variants:**

| Variant         | Meaning                                                    |
|-----------------|------------------------------------------------------------|
| `Direct`        | Unambiguous: exactly one rule matches this token           |
| `Lookahead`     | Ambiguous: multiple rules share this token; use next token |
| `CrossCategory` | Source NT + operator token                                 |
| `Cast`          | Parse source category, wrap in constructor                 |
| `Grouping`      | Parenthesized expression                                   |
| `Variable`      | Identifier fallback                                        |

### 3.5 Decision Tree (PathMap Trie)

The PathMap-based decision tree (Dylon, 2025) replaces 7 ad-hoc dispatch
optimizations with a single unified mechanism.  Rule prefixes are encoded
as byte sequences and inserted into a trie; at each node, the trie
determines whether dispatch is deterministic or requires disambiguation.

**Byte encoding scheme:**

```
0x00..0x7F  Terminal token IDs (from TokenIdMap)
0x80        IDENT_CAPTURE    — consumes one Ident token
0x81        BINDER_CAPTURE   — consumes one Ident (binding site)
0x82..0xBF  NonTerminal IDs  — 0x82 + category_index (triggers segment split)
0xC0        OPTIONAL_START   — begins optional group
0xC1        OPTIONAL_END     — ends optional group
```

**Segment architecture:** The trie is split at nonterminal boundaries into
linked segments.  Segment 0 is the root (terminal-only prefix).  When a
nonterminal is encountered, parsing dispatches to the nonterminal's category,
then continues in a continuation segment indexed by the nonterminal's FIRST
set.

**Three dispatch modes:**

| Mode             | Condition                            | Behavior                                 |
|------------------|--------------------------------------|------------------------------------------|
| `Commit`         | Single unambiguous rule              | Direct dispatch, no backtracking         |
| `DisjointSuffix` | FIRST sets of continuations disjoint | Use suffix token to select               |
| `NfaTryAll`      | Overlapping continuations            | Try all candidates, backtrack on failure |

**DecisionAction lattice algebra:**

```
DecisionAction variants:
  Commit { rule_label, category, weight }     — deterministic dispatch
  Ambiguous { candidates }                     — multiple candidates
  NonterminalBoundary { options }              — dispatch on FIRST expansion

Lattice operations:
  pjoin(Commit(A), Commit(B)) = Ambiguous([A, B])   // merge: add ambiguity
  pjoin(Commit(A), Ambiguous(xs)) = Ambiguous([A] ∪ xs)
  pjoin(Ambiguous(xs), Ambiguous(ys)) = Ambiguous(xs ∪ ys)

  pmeet(Ambiguous(xs), Commit(A)) = Commit(A) if A ∈ xs, else ∅
  psubtract(Ambiguous(xs), Commit(A)) = Ambiguous(xs \ {A})
```

This lattice enables incremental trie updates: inserting a new rule computes
`pjoin` at each trie node along the path, and removing a rule computes
`psubtract`.

**TreeStats** for analysis:

```rust
pub struct TreeStats {
    pub total_states: usize,
    pub deterministic_nodes: usize,
    pub ambiguous_nodes: usize,
    pub max_depth: usize,
    pub min_lookahead: usize,        // minimum tokens for deterministic dispatch
    pub nonterminal_boundaries: usize,
    pub shared_prefix_savings: usize,
    pub total_rules: usize,
    pub deterministic_rules: usize,
}
```

---

## 4. Semiring Framework

All weighted analysis in PraTTaIL is parameterized over semirings.
A semiring (K, ⊕, ⊗, 0̄, 1̄) provides two operations — ⊕  combines parallel
alternatives, ⊗  sequences path segments — subject to four axioms:

1. (K, ⊕, 0̄) is a commutative monoid
2. (K, ⊗, 1̄) is a monoid
3. ⊗  distributes over ⊕
4. 0̄ annihilates: 0̄ ⊗  a = a ⊗  0̄ = 0̄

### 4.1 Trait Hierarchy

```
Semiring: Clone + Copy + Debug + PartialEq + Send + Sync + 'static
  ├── fn zero() -> Self                   // 0̄
  ├── fn one() -> Self                    // 1̄
  ├── fn plus(&self, other: &Self) -> Self   // ⊕
  ├── fn times(&self, other: &Self) -> Self  // ⊗
  ├── fn is_zero(&self) -> bool
  ├── fn is_one(&self) -> bool
  └── fn approx_eq(&self, other: &Self, epsilon: f64) -> bool
      │
      ├── DetectableZero (marker)
      │     O(1) reliable is_zero() check
      │
      ├── IdempotentSemiring (marker)
      │     a ⊕  a = a  (enables fixed-point convergence)
      │
      ├── CompleteSemiring (marker)
      │     Infinite sums well-defined
      │
      └── StarSemiring
            fn star(&self) -> Self       // a* = 1̄ ⊕  a ⊕  a² ⊕  ...
            fn plus_star(&self) -> Self  // a⁺ = a ⊗  a*

HeapSemiring: Clone + Debug + PartialEq + Send + Sync + 'static
  (same operations, without Copy bound — for HashMap-backed weights)
```

### 4.2 Feature Matrix 1a: Semiring Algebra

| Name                   | Carrier Set       | ⊕                | ⊗              | 0̄        | 1̄          | Feature  |
|------------------------|-------------------|------------------|----------------|----------|------------|----------|
| TropicalWeight         | ℝ₊ ∪ {+∞}         | min(a,b)         | a + b          | +∞       | 0.0        | core     |
| CountingWeight         | ℕ (u64)           | a + b            | a × b          | 0        | 1          | core     |
| BooleanWeight          | {false, true}     | a ∨ b            | a ∧ b          | false    | true       | core     |
| EditWeight             | ℕ ∪ {∞} (u32)     | min(a,b)         | a + b          | u32::MAX | 0          | core     |
| ProductWeight\<S1,S2\> | S1 × S2           | component-wise   | component-wise | (0̄₁, 0̄₂) | (1̄₁, 1̄₂)   | core     |
| ContextWeight          | 𝒫(Labels) 128-bit | a ∪ b            | a ∩ b          | ∅        | U          | core     |
| ComplexityWeight       | ℕ ∪ {∞} (u32)     | min(a,b)         | max(a,b)       | u32::MAX | 0          | core     |
| ViterbiWeight          | [0, 1]            | max(a,b)         | a × b          | 0.0      | 1.0        | core     |
| ArcticWeight           | ℝ ∪ {-∞}          | max(a,b)         | a + b          | -∞       | 0.0        | core     |
| FuzzyWeight            | [0, 1]            | max(a,b)         | min(a,b)       | 0.0      | 1.0        | core     |
| TruncationWeight\<K\>  | {0, ..., K}       | max(a,b)         | min(a+b, K)    | 0        | 0          | core     |
| NbestWeight\<N\>       | Top-N paths       | merge_nbest      | cross_nbest    | ∅        | {(0, 0.0)} | core     |
| TensorWeight\<W1,W2\>  | Σᵢ w1ᵢ ⊗  w2ᵢ     | concat+simplify  | bilinear       | ∅        | 1₁ ⊗  1₂   | core     |
| LogWeight              | ℝ₊ ∪ {+∞}         | -ln(e⁻ᵃ + e⁻ᵇ)   | a + b          | +∞       | 0.0        | wfst-log |
| EntropyWeight          | (ℝ₊ ∪ {+∞}) × ℝ   | (logsumexp, mix) | (add, add)     | (+∞, 0)  | (0, 0)     | wfst-log |
| AmplitudeWeight        | ℂ                 | z₁ + z₂          | z₁ × z₂        | 0+0i     | 1+0i       | quantum  |

**Heap-allocated (HeapSemiring):**

| Name                   | Carrier Set       | ⊕             | ⊗             | Feature           |
|------------------------|-------------------|---------------|---------------|-------------------|
| MultisetWeight         | ℕ₀^F (HashMap)    | pointwise max | pointwise add | multiset-automata |
| TropicalMultisetWeight | ℝ₊^F∞ (HashMap)   | pointwise min | pointwise add | multiset-automata |
| RelationalWeight\<G\>  | 2^{G×G} (HashSet) | R₁ ∪ R₂       | R₁ ; R₂       | wpds-relational   |
| ProvenanceWeight       | N[X] (BTreeMap)   | poly add      | poly multiply | provenance        |

### 4.3 Feature Matrix 1b: Semiring Properties

| Name                  | Idempotent | Complete | Star | DetectZero | Copy | Feature  |
|-----------------------|:----------:|:--------:|:----:|:----------:|:----:|----------|
| TropicalWeight        |     ✓      |    ✓     |  ✓   |     ✓      |  ✓   | core     |
| CountingWeight        |     ✗      |    ✗     |  ✓   |     ✓      |  ✓   | core     |
| BooleanWeight         |     ✓      |    ✓     |  ✓   |     ✓      |  ✓   | core     |
| EditWeight            |     ✓      |    ✓     |  ✓   |     ✓      |  ✓   | core     |
| ProductWeight         |    ✓/✗     |   ✓/✗    | ✓/✗  |     ✓      |  ✓   | core     |
| ContextWeight         |     ✓      |    ✓     |  ✓   |     ✓      |  ✓   | core     |
| ComplexityWeight      |     ✓      |    ✓     |  ✓   |     ✓      |  ✓   | core     |
| ViterbiWeight         |     ✓      |    ✓     |  ✓   |     ✓      |  ✓   | core     |
| ArcticWeight          |     ✓      |    ✓     |  ✓   |     ✓      |  ✓   | core     |
| FuzzyWeight           |     ✓      |    ✓     |  ✓   |     ✓      |  ✓   | core     |
| TruncationWeight\<K\> |     ✓      |    ✓     |  ✗   |     ✓      |  ✓   | core     |
| NbestWeight\<N\>      |     ✗      |    ✗     |  ✗   |     ✓      |  ✓   | core     |
| TensorWeight          |    ✓/✗     |   ✓/✗    | ✓/✗  |     ✓      |  ✓   | core     |
| LogWeight             |     ✗      |    ✓     |  ✓   |     ✓      |  ✓   | wfst-log |
| EntropyWeight         |     ✗      |    ✓     |  ✓   |     ✓      |  ✓   | wfst-log |
| AmplitudeWeight       |     ✗      |    ✗     |  ✗   |     ✓      |  ✓   | quantum  |

(ProductWeight/TensorWeight inherit properties when both components satisfy them.)

### 4.4 Feature Matrix 1c: Semiring Usage Map

| Name                  | Primary Consumer(s)               | What It Computes                        |
|-----------------------|-----------------------------------|-----------------------------------------|
| TropicalWeight        | WFST dispatch, recovery, WPDS     | Shortest path / minimum cost            |
| CountingWeight        | Ambiguity analysis, CEGAR tier 2  | Number of derivation paths              |
| BooleanWeight         | Dead-rule detection, CEGAR tier 1 | Reachability (yes/no)                   |
| EditWeight            | Recovery cost                     | Edit distance (token-level)             |
| ProductWeight\<A,B\>  | Multi-criteria optimization       | Lexicographic: A then B                 |
| ContextWeight         | Follow-set tightening             | Powerset intersection                   |
| ComplexityWeight      | Lookahead budget                  | Bottleneck complexity                   |
| ViterbiWeight         | Recovery confidence               | Direct probability (most-probable path) |
| ArcticWeight          | Critical-path analysis            | Longest path / maximum benefit          |
| FuzzyWeight           | Dispatch confidence               | Possibilistic degree                    |
| TruncationWeight\<K\> | Tiered severity                   | Bounded ambiguity count                 |
| NbestWeight\<N\>      | Parse forest, confidence gap      | Top-N derivation paths                  |
| TensorWeight          | Multi-pass WFST fusion            | Cost-level × derivation distribution    |
| LogWeight             | Training, forward-backward        | Log-probability (numerically stable)    |
| EntropyWeight         | Lint W09, adaptive beam           | Shannon entropy                         |
| AmplitudeWeight       | Quantum CTMC (MeTTaIL-Gillespie)  | Complex amplitude                       |
| MultisetWeight        | Process multiplicity              | Feature cardinality                     |
| RelationalWeight\<G\> | Boolean program analysis          | State-pair relations                    |
| ProvenanceWeight      | Derivation tracking               | How-provenance polynomials              |

### 4.5 Matrix Star

The `matrix_star<W: StarSemiring>(adj: &[Vec<W>]) -> Vec<Vec<W>>` function
implements generalized Floyd-Warshall over any star semiring (O(n³)).
`result[i][j]` computes the ⊕-sum of ⊗-products along all paths from `i` to `j`.

**Semiring-specific interpretations:**

| Semiring       | matrix_star computes                      |
|----------------|-------------------------------------------|
| BooleanWeight  | Reflexive-transitive reachability closure |
| TropicalWeight | All-pairs shortest paths                  |
| ArcticWeight   | All-pairs longest paths (critical path)   |
| CountingWeight | All-pairs path counts                     |
| EditWeight     | All-pairs minimum edit distance           |

**Conversion:** `ViterbiWeight(p) ↔ TropicalWeight(-ln(p))` via `from_tropical`/`to_tropical`.

---

## 5. Weighted Automata Layers

### 5.1 Prediction WFST

Each grammar category gets a `PredictionWfst` — a small weighted DFA that maps
input tokens to weighted dispatch actions.

**Structure:**

```rust
struct PredictionWfst {
    category: String,
    states: Vec<WfstState>,        // WFST states
    start: WfstStateId,            // start state
    actions: Vec<WeightedAction>,  // action table
    token_map: TokenIdMap,         // shared token → ID mapping
    beam_width: Option<TropicalWeight>,  // optional pruning threshold
    context_labels: HashMap<String, u8>, // rule → bit position (ContextWeight)
}
```

**Weight assignment strategy:**

| Dispatch Scenario               | Weight                         |
|---------------------------------|--------------------------------|
| Unambiguous token               | 0.0 (tropical one — zero cost) |
| Ambiguous, by declaration order | 0.0, 0.1, 0.2, ...             |
| Cross-category unique           | 0.0                            |
| Cross-category with backtrack   | 0.5                            |

**Topology:** Single-token dispatch uses `start → accept`.  Two-token
disambiguation uses `start ──(token₁)──→ intermediate ──(token₂)──→ accept`.

**Example WFST** for a 3-rule category:

```
            "+"         "+"          "-"
  start ──────→ s1 ──────→ s2    start ──────→ s3
          w=0.0    w=0.1            w=0.0
          [Add]    [Pos]            [Neg]

  Rule Add: dispatched on "+" with weight 0.0 (preferred)
  Rule Pos: dispatched on "+" with weight 0.1 (second choice)
  Rule Neg: dispatched on "-" with weight 0.0 (unambiguous)
```

**ContextWeight (128-bit bitset):** For ambiguous dispatch groups, each rule
gets a sequential bit position.  The ContextWeight tracks which rules are
"alive" after consuming tokens, enabling context-aware dead-token filtering.

### 5.2 Weighted Pushdown System (WPDS)

WPDS models the full parse call structure as a weighted pushdown system,
enabling stack-aware reachability analysis (Reps, Lal, & Kidd 2007).

**Stack symbol:**

```
⟨category.rule_label@position⟩
```

A stack symbol identifies a specific point in parsing: which category, which
rule, and which position within the rule's syntax items.

**Three rule types:**

| Rule Type | Form                 | Meaning                                  |
|-----------|----------------------|------------------------------------------|
| Replace   | ⟨p, γ⟩ ↪ ⟨p', γ'⟩    | Intraprocedural: advance within a rule   |
| Push      | ⟨p, γ⟩ ↪ ⟨p', γ'γ''⟩ | Cross-category call: push return address |
| Pop       | ⟨p, γ⟩ ↪ ⟨p', ε⟩     | Return: pop stack, resume caller         |

**Algorithms:**

- **poststar**: Forward reachability from initial configuration.  Saturates a
  P-automaton by adding transitions for each applicable rule.  Complexity:
  O(|Δ| × |Q₀| × H) where H is the height of the weight domain.
- **prestar**: Backward reachability to target configurations.  For each rule,
  adds transitions connecting sources to targets via weight accumulation.

**WPDS encoding example** for a 2-category grammar (Expr, Type):

```
Stack alphabet Γ:
  ⟨Expr⟩            — entry to Expr category
  ⟨Expr.Add@0⟩      — Add rule, before first operand
  ⟨Expr.Add@1⟩      — Add rule, after first operand (before "+")
  ⟨Expr.Add@2⟩      — Add rule, after "+" (before second operand)
  ⟨Type⟩            — entry to Type category
  ⟨Type.Arrow@0⟩    — Arrow rule, before domain type

Rules Δ:
  ⟨p, ⟨Expr⟩⟩ ↪ ⟨p, ⟨Expr.Add@0⟩⟩         (Replace: enter Add rule)
  ⟨p, ⟨Expr.Add@0⟩⟩ ↪ ⟨p, ⟨Expr⟩⟨Expr.Add@1⟩⟩  (Push: parse LHS Expr)
  ⟨p, ⟨Expr.Add@1⟩⟩ ↪ ⟨p, ⟨Expr.Add@2⟩⟩     (Replace: consume "+")
  ⟨p, ⟨Expr.Add@2⟩⟩ ↪ ⟨p, ⟨Expr⟩⟩           (Push: parse RHS Expr)
  ⟨p, ⟨Expr.Add@2⟩⟩ ↪ ⟨p, ε⟩                (Pop: rule complete)
```

**Call graph analysis:**

- `extract_call_graph()` — linear scan of Push rules + Tarjan SCC (strongly connected component) decomposition
- `WpdsCallGraph` — fan-in, fan-out, SCCs per category
- Recursion depth bounds, cycle classification, witness traces

**WpdsAnalysis** output feeds:
- W13 lint (WPDS-unreachable rules)
- W14 lint (WPDS-confirmed ambiguity via stringsum)
- D14 lint (complexity metrics)
- PipelineAnalysis.dead_rule_labels (Tier 5 DCE)

### 5.3 Token Lattice

`TokenSource<T, S>` is the parser's primary input abstraction:

| Variant                          | Overhead                   | Use Case                  |
|----------------------------------|----------------------------|---------------------------|
| `Linear(Vec<(T, S)>)`            | Zero (transparent wrapper) | ~100% of current grammars |
| `Lattice(TokenLattice<T, S, W>)` | Weighted DAG               | Lexically ambiguous input |

The lattice supports semiring-generic Viterbi decoding:

```
fn viterbi_generic<T, S, W: Semiring + Ord>(
    lattice: &TokenLattice<T, S, W>,
    final_node: usize,
) -> Option<ViterbiPath<T, S, W>>
```

**Algorithm:** Standard DAG dynamic programming (O(V+E)).  Forward pass
computes `dist[i]` = minimum-weight path from node 0 to node i, then
backtrace reconstructs the best path.

**Lattice example** for ambiguous `>>` tokenization:

```
         ">"         ">"
  0 ────────→ 1 ────────→ 2     (two separate > tokens)
       w=0.0       w=0.0

         ">>"
  0 ────────────────────→ 2     (single >> operator)
              w=0.0

  Viterbi selects lowest-weight path to node 2.
```

**N-best paths** (feature `wfst-log`): Simplified Eppstein's algorithm
returns up to N paths sorted by weight.

### 5.4 Error Recovery

Error recovery generates weighted repair actions.  The cost model uses
`ProductWeight<TropicalWeight, EditWeight>` — tropical cost first (parse
quality), edit-distance as tiebreaker (repair minimality).

**Repair action costs:**

| Action         | Tropical Cost | Edit Cost | Description                    |
|----------------|---------------|-----------|--------------------------------|
| Skip           | 0.5/token     | 1/token   | Advance past unexpected tokens |
| Delete         | 1.0           | 1         | Ignore one token               |
| Swap           | 1.25          | 2         | Reorder adjacent tokens        |
| Substitute     | 1.5           | 1         | Replace with expected token    |
| Insert         | 2.0           | 1         | Fabricate missing token        |
| CategorySwitch | 0.375         | 1         | Re-parse in different category |

**Recovery tiers:**

1. **Tier 1** — Context scaling: depth (deep nesting → discount skip),
   binding power (low BP → discount skip), frame kind (collection/group →
   discount insert)
2. **Tier 2** — Prediction-aware: discount factors from PredictionWfst
   confidence, bracket mismatch penalties
3. **Tier 3** — Simulation: validate repair by attempting continued parse
4. **Tier 4** — Forward-backward: semiring-generic hot-path recovery weight
   scaling
5. **Tier 5** — WPDS-guided: stack-aware recovery using poststar reachability

**RecoveryConfig** provides 20+ tunable parameters for cost modulation:

```rust
pub struct RecoveryConfig {
    // Base costs
    pub skip_per_token: f64,       // default: 0.5
    pub delete_cost: f64,          // default: 1.0
    pub substitute_cost: f64,      // default: 1.5
    pub insert_cost: f64,          // default: 2.0
    pub swap_cost: f64,            // default: 1.25
    pub max_skip_lookahead: usize, // default: 32

    // Tier 1: Depth scaling
    pub deep_nesting_threshold: usize,  // 1000 — discount skip above this
    pub deep_nesting_skip_mult: f64,    // 0.5
    pub shallow_depth_threshold: usize, // 10 — penalize skip below this
    pub shallow_depth_skip_mult: f64,   // 2.0

    // Tier 1: BP scaling
    pub low_bp_threshold: u8,           // 4 — discount skip below this BP
    pub low_bp_skip_mult: f64,          // 0.75

    // Tier 1: Frame-kind multipliers
    pub collection_insert_mult: f64,    // 0.5 (collections expect more elements)
    pub group_insert_mult: f64,         // 0.5 (groups expect closing delimiter)
    pub bracket_insert_mult: f64,       // 0.3 (brackets are cheap to insert)
    pub mixfix_substitute_mult: f64,    // 0.75 (mixfix parts are structural)

    // Tier 3: Simulation
    pub simulation_valid_mult: f64,     // 0.5 (valid continuation discount)
    pub simulation_fail_penalty: f64,   // 0.2 (per unmatched token)

    // Beam pruning
    pub beam_width: Option<f64>,        // Some(3.0) — prune repairs > best + 3.0

    // Cascade prevention
    pub cascade_window: usize,          // 3 — suppress errors within 3 tokens

    // B2: Adaptive modulation
    pub adaptive_weight_threshold: f64, // 1.0
    pub deterministic_skip_discount: f64, // 0.75 (when weight < threshold)
    pub ambiguous_insert_discount: f64,   // 0.5 (when weight ≥ threshold)
}
```

**RecoveryWfst** per-category structure:

```rust
pub struct RecoveryWfst {
    category: String,
    sync_tokens: BTreeSet<TokenId>,         // FOLLOW + structural delimiters
    token_map: TokenIdMap,
    prediction_discounts: HashMap<TokenId, f64>,  // B1: from PredictionWfst
    follow_contexts: HashMap<TokenId, ContextWeight>, // A1: rule-specific sync
    bracket_mismatch_ids: BTreeSet<TokenId>,      // A2: penalty tokens
    recursive_category: bool,                      // C2: SCC participation
}
```

### 5.5 Stream-to-Lattice Weight Assignment

> **Expanded treatment**: [Stream-to-Lattice Conversion](../theory/wfst/stream-to-lattice.md)
> — full derivations, rationale, worked examples, and semiring composition modes.
> **Architecture walkthrough**: [Stream-to-Lattice Architecture](../architecture/wfst/stream-to-lattice.md)
> — code-path walkthrough with source-line references for all 14 methods.

PraTTaIL converts sequential token streams into lattice-like structures at
**7 conversion points**, using **14 weight assignment methods** across
**10 semiring types** and **5 implicit lattice structures**. This subsection
is a compact catalog; see the companion documents linked above for full
derivations and rationale.

#### 5.5.1 Three-Phase Lifecycle

Weight assignment spans three lifecycle phases:

| Phase        | # Methods | IDs   | Semirings Used                                                                              | When                         |
|--------------|:---------:|-------|---------------------------------------------------------------------------------------------|------------------------------|
| Compile-time |     9     | A1–A9 | TropicalWeight, CountingWeight, BooleanWeight, ContextWeight, ComplexityWeight, NbestWeight | `cargo build` (pipeline)     |
| Runtime      |     5     | B1–B5 | TropicalWeight, EditWeight, ProductWeight, any `W: Semiring`                                | Parse time                   |
| Training     |     2     | C1–C2 | LogWeight, EntropyWeight                                                                    | Offline (`wfst-log` feature) |

#### 5.5.2 Weight Method Catalog

| ID | Name                  | Semiring          | Formula / Key Idea                                         | Cross-Ref                                                 |
|----|-----------------------|-------------------|------------------------------------------------------------|-----------------------------------------------------------|
| A1 | Lexical priority      | TropicalWeight    | w = 10.0 − priority(token)                                 | [§5.1](#51-prediction-wfst) (dispatch weight table)       |
| A2 | Action type weight    | TropicalWeight    | Fixed table: Direct=0.0, CrossCat+bt=0.5, Variable=2.0     | [§5.1](#51-prediction-wfst) (dispatch weight table)       |
| A3 | Rule specificity      | TropicalWeight    | w = 1/(1 + t + 0.5n)                                       | [§5.1](#51-prediction-wfst) (dispatch weight table)       |
| A4 | Dispatch composition  | TropicalWeight    | w_final = w_action ⊗  w_specificity (tropical +)           | [§5.1](#51-prediction-wfst) (AMBIGUOUS_WEIGHTS)           |
| A5 | Derivation counting   | CountingWeight    | count = \|{r : token ∈ FIRST(r)}\|                         | Ambiguity diagnostics (W05)                               |
| A6 | Reachability          | BooleanWeight     | reachable(C) = ∃ path from root to C                       | Dead-rule diagnostics                                     |
| A7 | Context tracking      | ContextWeight     | context(s) = ⊕{singleton(label_i)}  (128-bit bitset)       | Grammar overlap analysis                                  |
| A8 | Bottleneck complexity | ComplexityWeight  | bottleneck(path) = max(complexity_i)                       | Lookahead diagnostics                                     |
| A9 | N-best tracking       | NbestWeight\<N\>  | top-N merge + confidence gap Δ = w₂ − w₁                   | Confidence gap diagnostics                                |
| B1 | Repair costs          | TropicalWeight    | skip=0.5, del=1.0, swap=1.25, sub=1.5, ins=2.0 + modifiers | [§5.4](#54-error-recovery) (repair tiers, RecoveryConfig) |
| B2 | Edit distance         | EditWeight        | skip/del=1, ins/sub=2 (integer count)                      | [§5.4](#54-error-recovery) (RecoveryCost)                 |
| B3 | Dual-cost recovery    | ProductWeight     | (w_tropical, n_edits) — lexicographic Viterbi              | [§5.4](#54-error-recovery) (RecoveryCost)                 |
| B4 | Identity assignment   | any `W: Semiring` | ∀ token: w = W::one()                                      | [§5.3](#53-token-lattice) (linear_to_lattice)             |
| B5 | Position penalty      | TropicalWeight    | w += \|Δpos\| × 0.5                                        | NFA disambiguation (from_alternatives)                    |
| C1 | Probabilistic (log)   | LogWeight         | w = −ln(p); SGD update via forward-backward                | Training (wfst-log gate)                                  |
| C2 | Entropy               | EntropyWeight     | (−ln(p), −ln(p)); H = −Σ pᵢ ln(pᵢ)                         | Adaptive beam width (wfst-log gate)                       |

#### 5.5.3 Seven Conversion Points

The pipeline has seven places where sequential data becomes lattice-like:

```
Input string
     │
     ├─① lex_core()           &str → Vec<(Token, Range)>              [always-on]
     ├─② lex_weighted_core()  &str → Vec<(Token, Range, f64)>         [always-on]
     ├─③ lex_lattice_core()   &str → TokenSource::Linear|Lattice      [always-on]
     │
     ├─④ from_weighted()      weighted triples → TokenSource::Linear   [always-on]
     ├─⑤ resolve()/beam()     TokenSource → Vec<(T,S)>  (Viterbi)     [always-on]
     │
     ├─⑥ viterbi_multi_step() [TokenId] + sync → RepairSequence       [on parse error]
     └─⑦ from_alternatives()  Vec<Cat> → single Cat                    [on NFA ambiguity]
```

Points ①–③ are lexer-level (text → tokens); ④–⑤ collapse lattice to flat
stream; ⑥–⑦ are parser-level implicit lattices.

#### 5.5.4 Five Implicit Lattice Structures

Five places use lattice semantics without instantiating `TokenLattice`:

| # | Structure                  | Representation                         | Lattice Shape               | Lifecycle    |
|---|----------------------------|----------------------------------------|-----------------------------|--------------|
| A | Recovery repair trellis    | `Vec<RecoveryCost>` arrays             | Forward trellis (≤32 nodes) | Runtime      |
| B | NFA spillover buffer       | `Cell<Vec<(Cat, usize, f64)>>`         | 2-node, N parallel edges    | Runtime      |
| C | Dispatch weight maps       | `HashMap<(Cat, TokenId), Vec<Action>>` | Per-token fan-out           | Compile-time |
| D | Forward-backward adjacency | `Vec<Vec<(usize, W)>>`                 | Generic DAG over WFST states| Training     |
| E | WFST transitions           | `Vec<WfstState>`                       | Full automaton DAG          | Compile-time |

#### 5.5.5 Weight Flow Lifecycle

Compile-time weights are baked into generated code; runtime methods operate
over those baked-in values; training methods can update them via a feedback loop.

```
┌────────────────────── Compile Time ──────────────────────┐
│                                                          │
│  A1 (priority) ─► accept_weight()  [DFA states]          │
│  A2 (action) ──┐                                         │
│  A3 (specific) ┴► A4 (compose) ─► AMBIGUOUS_WEIGHTS      │
│  A5–A9 ────────────────────────► diagnostics only        │
│                      │                                   │
└──────────────────────┊───────────────────────────────────┘
                       │  baked into generated match arms
┌──────────────────────┊───────────────────────────────────┐
│                      ▼            Runtime                │
│                                                          │
│  B1–B3 (repair) ──► viterbi_multi_step()   [structure A] │
│  B4 (identity)  ──► linear_to_lattice()    [structure D] │
│  B5 (position)  ──► from_alternatives()    [structure B] │
│                                                          │
│  WEIGHT_CORRECTIONS ◄── from_alternatives() feedback     │
│        │                                                 │
└────────┊─────────────────────────────────────────────────┘
         │  drain after parsing
┌────────┊─────────────────────────────────────────────────┐
│        ▼            Training (wfst-log)                  │
│                                                          │
│  C1 (log)     ──► SGD weight update                      │
│  C2 (entropy) ──► adaptive beam width                    │
│        │                                                 │
│        └──► retrained weights ──► re-pipeline            │
└──────────────────────────────────────────────────────────┘
```

#### 5.5.6 Worked Example: `float` Dispatch

Trace `float(1 == 1)` through weight computation (RhoCalc grammar):

```
① lex_weighted_core():  Ident("float") → w_lex = 0.0  (no lexical ambiguity)

② Compile-time dispatch weights (baked in):
     FloatCast:    w_action(A2) = 0.0 (Direct)
                   w_spec(A3)   = 1/(1+1+0.5) = 0.40
                   w_final(A4)  = 0.0 + 0.40 = 0.40

     FunctionCall: w_action(A2) = 0.5 (CrossCat+backtrack)
                   w_spec(A3)   = 1/(1+1+0.75) ≈ 0.36
                   w_final(A4)  = 0.5 + 0.36 ≈ 0.86

③ NFA spillover (structure B):
     Primary:   FloatCast     (w=0.40)  ← weight-best, tried first
     Spillover: FunctionCall  (w≈0.86)  ← tried if primary fails

④ from_alternatives() (conversion point ⑦):
     Both accept → argmin weight → FloatCast (0.40 < 0.86)
     Result: FloatCast(EqExpr(Int(1), Int(1)))
```

#### 5.5.7 Theoretical Basis

The weight assignment framework rests on two theoretical pillars:

- **Mohri (2009)** — Weighted automata algorithms: tropical shortest-path
  (Viterbi), log-semiring forward-backward, and ε-removal over general
  semirings. Justifies A1–A4, B1–B3, C1. (See [Appendix E](#e-references).)

- **Droste, Kuich, & Vogler (2009)** — *Handbook of Weighted Automata*:
  semiring axioms, product semiring constructions, star semiring closure.
  Justifies the ProductWeight composition (B3), StarSemiring matrix closure
  (`matrix_star`), and the diagnostic semirings A5–A9. (See [Appendix E](#e-references).)

---

## 6. Analysis and Optimization

### 6.1 Cost-Benefit Framework

Every optimization in PraTTaIL is registered in the `Optimization` enum
(63 variants) and scored via `ProductWeight<TropicalWeight, TropicalWeight>` —
lexicographic ordering of (estimated speedup, compile cost).  Among equally
beneficial optimizations, the cheaper one is preferred.

```rust
pub struct OptimizationCandidate {
    pub optimization: Optimization,
    pub speedup: TropicalWeight,       // lower = more beneficial
    pub compile_cost: TropicalWeight,  // lower = cheaper
    pub score: ProductWeight<TropicalWeight, TropicalWeight>,
    pub applicable: bool,
    pub reason: String,
}
```

**Feature Matrix 2: Key Optimization Gates**

| ID    | Name                    | Applicability                     | Layer          |
|-------|-------------------------|-----------------------------------|----------------|
| A1    | LeftFactoring           | shared_prefix_ratio > 0.3         | Dispatch       |
| A2    | HotColdSplitting        | cold_fraction > 0.4               | Dispatch       |
| A4    | EnhancedDCE             | always                            | Pipeline       |
| A5    | AmbiguityTargeting      | ambiguous_count > 0               | Pipeline       |
| B1    | MultiTokenLookahead     | ambiguous_fraction > 0.1          | WFST           |
| B3    | WfstMinimization        | always                            | WFST           |
| F1    | SpilloverPruning        | nfa_spillover > 0                 | NFA            |
| G1    | BacktrackingElimination | always                            | Parser         |
| BP02  | TailCallElim            | tail-eligible rules exist         | Parser         |
| BP03  | BpTableLookup           | ≥ 8 operators                     | Parser         |
| BP05  | BpRangeLoop             | BP range fits in 16 bits          | Parser         |
| CD02  | SegmentMerging          | NT boundaries with disjoint FIRST | Decision Tree  |
| ART01 | HashConsing             | categories with recursive terms   | Ascent Runtime |
| ART06 | DemandDriven            | unreferenced categories exist     | Ascent Codegen |
| AL02  | HybridLexer             | dead_fraction > threshold         | Lexer          |
| AL04  | KeywordMph              | ≥ 4 keywords                      | Lexer          |

**Full optimization layer taxonomy:**

| Layer    | ID Range      | Count | Target                                                      |
|----------|---------------|-------|-------------------------------------------------------------|
| ART      | ART01-ART06   | 6     | Ascent runtime (allocation, iteration, memory)              |
| BCG      | BCG01-BCG06   | 6     | Ascent codegen (join order, fusion, pruning)                |
| AL       | AL01-AL06     | 6     | Lexer (repacking, hybrid, SIMD, MPH, chains)                |
| BP       | BP01-BP05     | 5     | Binding power (compaction, tail-call, table, inline, range) |
| CD       | CD01-CD05     | 5     | Dispatch (frequency, merge, goto, threading, CSE)           |
| DB       | DB01-DB04     | 4     | Pipeline (incremental, lazy, parallel, cache)               |
| Core     | A1-G25, F1-H1 | 15    | WFST/NFA/dispatch framework                                 |
| Analysis | T01-PD01      | 16    | Feature-gated verification                                  |

**Optimization evaluation:** `evaluate_optimizations()` builds a
`GrammarProfile` from PredictionWfst analysis, PathMap decision trees, and
NFA spillover data, then scores each optimization candidate.

```rust
pub fn build_grammar_profile(
    prediction_wfsts: &HashMap<String, PredictionWfst>,
    first_sets: &HashMap<String, FirstSet>,
    nfa_spillover_cats: &HashSet<String>,
    rule_count: usize,
    has_beam_width: bool,
    decision_trees: &HashMap<String, CategoryDecisionTree>,
) -> GrammarProfile
```

The profile captures:
- `shared_prefix_ratio` (0.0..1.0) — fraction of rules sharing prefixes
- `cold_fraction` (0.0..1.0) — fraction of high-weight dispatch paths
- `ambiguous_fraction`, `ambiguous_count` — ambiguity metrics
- `category_count`, `rule_count` — grammar size
- `total_wfst_states`, `avg_trie_depth` — automata metrics
- `deterministic_ratio` — fraction of deterministic dispatch decisions

### 6.2 Lint Layer

PraTTaIL includes 120+ diagnostics organized by subsystem prefix.  Each
diagnostic has an ID, severity, and optional hint.

**Lint prefix categories:**

| Prefix | Domain                               | Example Codes                                                 |
|--------|--------------------------------------|---------------------------------------------------------------|
| A      | Ascent codegen                       | A01-A10                                                       |
| G      | Grammar structure                    | G01 left-recursion, G03 ambiguous-prefix, G07 identical-rules |
| W      | WFST analysis                        | W01 dead-rule, W03 high-ambiguity, W13 WPDS-unreachable       |
| R      | Recovery                             | R01 empty-sync-set, R05 missing-bracket-sync                  |
| C      | Cross-category                       | C01 cast-cycle, C04 wide-cross-overlap                        |
| X      | Composition                          | X01-X05                                                       |
| P      | Performance                          | P02 NFA-spillover, P04 many-alternatives                      |
| D      | Diagnostics                          | D10 lookahead-waste, D14 WPDS-complexity                      |
| LEX    | Lexer optimization                   | LEX02-LEX05                                                   |
| PAR    | Parser optimization                  | PAR01-PAR05                                                   |
| DIS    | Dispatch optimization                | DIS01-DIS05                                                   |
| I      | Infrastructure                       | I01, I04, I08, I10, I17, I18                                  |
| T      | TRS (term rewriting system) analysis | T01 non-joinable-pair, T02 non-terminating                    |
| V      | VPA analysis                         | V01 VPA-determinizable, V03 WTA-unrecognized                  |
| S      | Safety/CEGAR                         | S01 safety-violation, S03 CEGAR-iteration                     |
| N      | Concurrency                          | N01 Petri-deadlock, N06 alternating-anomaly                   |
| L      | LTL temporal                         | L01 LTL-violated, L02 LTL-satisfied                           |
| E      | Provenance/CRA                       | E01 provenance-gap, E02 CRA-anomaly                           |
| M      | Morphisms                            | M01 morphism-gap, M02 morphism-complete                       |
| K      | KAT                                  | K01 KAT-inequivalence, K02 KAT-equivalent                     |
| SYM    | Symbolic                             | SYM01 unsatisfiable-guard, SYM02 overlapping-guards           |
| O      | Omega/Buchi                          | O01 non-convergent, O02 heavy-cycle                           |
| PT     | Parity Tree                          | PT01 emptiness-violation, PT02 subsumption                    |
| RA     | Register                             | RA01 unbound-data, RA02 redundant-register                    |
| PR     | Probabilistic                        | PR01 low-selectivity, PR03 high-entropy                       |
| MT     | Multi-tape                           | MT01 channel-overlap, MT02 disconnected                       |
| MS     | Multiset                             | MS01 unsatisfiable-constraint                                 |
| MSO    | Weighted MSO                         | MSO01 unrestricted-quantifier                                 |
| TW     | Two-way                              | TW01 circular-dependency, TW02 one-way-sufficient             |
| PD     | Predicate dispatch                   | PD01 degenerate-predicate, PD03 dispatch-savings              |

**Environment variable controls:**

| Variable                | Values                             | Default   |
|-------------------------|------------------------------------|-----------|
| `PRATTAIL_LINT_LEVEL`   | `error`, `warning`, `note`, `info` | `warning` |
| `PRATTAIL_LINT_VERBOSE` | (any value to enable)              | disabled  |

When verbose is off, repeated lint IDs are grouped into compact summaries
with counts.  The output uses Rust-compiler-style ANSI coloring (red=error,
yellow=warning, cyan=note/info).

### 6.3 Dead-Rule Detection

Dead-rule detection uses a 5-tier hierarchy, each layer refining the previous:

```
Tier 1: Structural         LiteralNoNativeType (literal rule, no native type)
    │
    ▼
Tier 2: Graph              UnreachableCategory (category not reachable from root)
    │
    ▼
Tier 3: WFST               WfstUnreachable (zero-weight in prediction WFST)
    │
    ▼
Tier 4: Decision Tree      PathMap trie confirms unreachability
    │
    ▼
Tier 5: WPDS               Stack-aware reachability (poststar + prestar)
```

Semantic dependency groups from equations/rewrites provide transitive
liveness: if rule A is alive and references rule B's label, B is kept alive.

The final `dead_rule_labels` set feeds into:
- Ascent codegen: DCE (dead-code elimination) of Ascent Datalog rules
- Trampoline codegen: skip dead rule frame variants
- Decision tree: filter dead rules from insertion
- Lint output: W01 diagnostics

---

## 7. Advanced Automata Infrastructure

PraTTaIL provides 11 advanced automata modules plus a predicate dispatch
controller.  Each module is feature-gated and activated on demand based
on grammar predicate complexity.

### 7.1 Feature Dependency DAG

```
                        ┌──────────────┐
                        │ predicate-   │
                        │  dispatch    │
                        └──────┬───────┘
                               │
                    ┌──────────┴──────────┐
                    │                     │
             ┌──────▼──────┐      ┌───────▼───────┐
             │ symbolic-   │      │ weighted-mso  │
             │  automata   │      │               │
             └──────┬──────┘      └───────────────┘
                    │
                    │ depends on
                    │
              ┌─────▼─────┐
              │    kat    │
              └───────────┘

  ┌────────────────┐    ┌────────────────┐    ┌──────────────┐
  │ parity-tree-   │    │  register-     │    │ probabilistic│
  │  automata      │    │   automata     │    │              │
  └───────┬────────┘    └──────┬─────────┘    └──────┬───────┘
          │                    │                     │
    ┌─────┴──────┐        ┌────┴─────┐          ┌────┴─────┐
    │ alternating│        │ nominal  │          │ wfst-log │
    │            │        └──────────┘          └────┬─────┘
    └─────┬──────┘                                   │
          │                                    ┌─────┴──────────┐
    ┌─────┴──────────┐                   ┌─────▼──────┐  ┌──────▼──────┐
    │ tree-automata  │                   │ multi-tape │  │ two-way-    │
    └────────────────┘                   └────────────┘  │  transducer │
                                                         └─────────────┘

  ┌────────────────┐    ┌───────────┐
  │ multiset-      │    │   omega   │
  │  automata      │    │           │──→ ltl
  │ (standalone)   │    └───────────┘
  └────────────────┘
```

### 7.2 Feature Matrix 3: Advanced Automata Capabilities

| Module           | Feature Gate           | Decidable | Infinite-Domain | ω-Regular | Key Operations                                       |
|------------------|------------------------|:---------:|:---------------:|:---------:|------------------------------------------------------|
| M1 Symbolic      | `symbolic-automata`    |     ✓     |        ✓        |     ✗     | Minterm determinization, guard analysis              |
| M2 Buchi         | `omega`                |     ✓     |        ✗        |     ✓     | SCC cycle analysis, emptiness, Buchi product         |
| M3 Alternating   | `alternating`          |     ✓     |        ✗        |     ✓     | Game semantics, bisimulation, polynomial transitions |
| M4 VPA           | `vpa`                  |     ✓     |        ✗        |     ✗     | Determinization, equivalence, complement             |
| M5 Parity Tree   | `parity-tree-automata` |     ✓     |        ✗        |     ✓     | Zielonka solver, mu-calculus conversion              |
| M6 Register      | `register-automata`    |    ✓†     |        ✓        |     ✗     | Data equality, freshness, bounded emptiness          |
| M7 Probabilistic | `probabilistic`        |     ✓     |        ✗        |     ✗     | Forward/Viterbi/Baum-Welch, entropy                  |
| M8 Multi-Tape    | `multi-tape`           |     ✓     |        ✗        |     ✗     | K-tape product, tape projection, auto-intersect      |
| M9 Multiset      | `multiset-automata`    |     ✓     |        ✗        |     ✗     | Cardinality constraints, tropical projection         |
| M10 MSO          | `weighted-mso`         |    ✓‡     |        ✗        |     ✗     | Formula classification, B-E-T theorem                |
| M11 Two-Way      | `two-way-transducer`   |     ✓     |        ✗        |     ✗     | Bidirectional simulation, deadlock detection         |

† Register automata: decidable for bounded registers.
‡ Weighted MSO: decidable for the restricted fragment (no ∀X).

### 7.3 Per-Module Reference

Each module subsection includes: theory summary, key type, operations,
pipeline integration, and associated lints.

---

#### M1: Symbolic Finite Automata

**Source:** `symbolic.rs` (feature: `symbolic-automata`)

**Theory:** Symbolic automata replace explicit alphabet transitions with
predicate-labeled transitions over potentially infinite domains (D'Antoni &
Veanes 2017).  The core abstraction is the `BooleanAlgebra` trait.

**Key types:**

```rust
trait BooleanAlgebra {
    type Predicate;
    type Domain;
    fn true_pred() -> Self::Predicate;
    fn and(a, b) -> Self::Predicate;
    fn not(a) -> Self::Predicate;
    fn is_satisfiable(p) -> bool;
    fn witness(p) -> Option<Self::Domain>;
}
```

**Three concrete algebras:**

| Algebra             | Predicate       | Domain                  | Use Case                 |
|---------------------|-----------------|-------------------------|--------------------------|
| `KatBooleanAlgebra` | `BooleanTest`   | `HashMap<String, bool>` | Propositional guards     |
| `IntervalAlgebra`   | `IntervalPred`  | `i64`                   | Numeric range predicates |
| `CharClassAlgebra`  | `CharClassPred` | `char`                  | Structural patterns      |

**Key algorithm:** Minterm-based SFA determinization.  Minterms are the
atoms of the Boolean algebra of guards — maximal satisfiable conjunctions
of predicates and their negations.  Determinization proceeds by subset
construction over minterms, producing a deterministic SFA.

**Decidability tiers:** T1 (satisfiability-decidable), T2 (witness-decidable),
T3 (evaluation-decidable), T4 (undecidable).

**Applications:**
- `is_satisfiable()` tests guard predicates against the concrete
  `BooleanAlgebra` implementation; `witness()` produces a satisfying
  domain element for diagnostic examples (e.g., `IntervalAlgebra` on
  `x > 0 /\ x < 100` yields witness 50).  Minterm-based determinization
  partitions the guard space into maximal satisfiable atoms, enabling
  subset construction over predicates rather than enumerating the domain
  (critical for `CharClassAlgebra` over the 143,859-element Unicode
  `char` domain).
- Guard intersection analysis identifies overlapping predicates (e.g.,
  `x > 10` and `x < 20` share a non-empty range), dead guards (e.g.,
  `x > 5 /\ x < 3` is unsatisfiable), and subsumed guards (one logically
  implies another).  These feed DCE of unreachable code paths and
  compile-time resolution of predicate-dispatch ambiguity (e.g., Rholang
  `contract` pattern matching, MeTTa guarded rewrites).
- SYM01 flags unsatisfiable guards; SYM02 flags overlapping guards;
  SYM03 identifies subsumed guards; SYM04 flags non-minimal guard sets
  where minterm reduction could shrink the transition count.
- `analyze_from_bundle()` produces `SymbolicAnalysis` (guard
  satisfiability, overlap, minimality) wired into
  `LintContext.symbolic_result`, always-on as BASE dispatch bit 0.

**Lints:** SYM01 unsatisfiable-guard, SYM02 overlapping-guards, SYM03
subsumed-guard, SYM04 non-minimal-guards.

### 7.4 M2: Weighted Buchi Automata

**Source:** `buchi.rs` (feature: `omega`)

**Theory:** Buchi automata accept infinite words by requiring infinitely many
visits to accepting states (Buchi 1962).  Weighted Buchi automata assign
semiring weights to transitions and compute the total weight of accepting runs
over infinite-length inputs.

**Key type:**

```rust
struct WeightedBuchiAutomaton<W: Semiring> {
    states: Vec<BuchiState>,
    alphabet: HashSet<String>,
    transitions: HashMap<(StateId, String), Vec<(StateId, W)>>,
    initial_states: HashSet<StateId>,
    accepting_states: HashSet<StateId>,
}
```

**Operations:**
- `check_emptiness()` — nested DFS with SCC analysis
- `buchi_intersect()` — product construction for two NBAs
- `total_accepting_weight<W: StarSemiring>()` — matrix star closure
- `from_wpds()` — WPDS → NBA (nondeterministic Büchi automaton) conversion for poststar reachability

**Pipeline integration:** `from_wpds()` converts WPDS rules to NBA
transitions, enabling LTL model checking via the Buchi-WPDS product
construction.  Results feed O01-O02 lints for ω-regular property verification.

**Applications:**
- `check_emptiness()` performs nested DFS with SCC analysis to determine
  accepting-cycle reachability.  `buchi_intersect()` computes the product
  of two NBAs.  `total_accepting_weight()` applies matrix star closure
  over `StarSemiring`.  `from_wpds()` converts WPDS push/pop/replace
  rules to NBA transitions for LTL model checking via the Buchi-WPDS
  product construction.
- Accepting-SCC reachability determines liveness properties: persistent
  process responsiveness (e.g., Rholang `contract` liveness), eventuality
  guards (visiting "delivered" states infinitely often), and non-termination
  detection (infinite reduction cycles in rewrite systems).
- O01 flags non-convergent accepting cycles (infinite reduction sequences);
  O02 flags high-weight-ratio cycles (performance bottleneck candidates).
- `analyze_from_bundle()` produces `BuchiAnalysis` (cycle data,
  convergence metrics) wired into `LintContext.buchi_result`.  Activated
  by infinite quantifiers (`ForallInfinite`, `ExistsInfinite`) in
  predicate dispatch (estimated cost = 3).

**Lints:** O01 non-convergent, O02 heavy-cycle.

### 7.5 M3: Weighted Alternating Automata (AWA)

**Source:** `alternating.rs` (feature: `alternating`)

**Theory:** Alternating automata generalize nondeterminism by allowing both
existential (⊕) and universal (⊗) branching (Chandra, Kozen, & Stockmeyer
1981).

**Branching modes:**

| Mode             | Semantics                      | Weight Combination    |
|------------------|--------------------------------|-----------------------|
| Existential (Q⊕) | At least one successor accepts | ⊕  (select best)      |
| Universal (Q⊗)   | All successors must accept     | ⊗  (accumulate costs) |

**Polynomial transitions:** Successors are combined with coefficients,
enabling weighted game-theoretic analysis.

**Applications:**
- Q⊗  (universal) branching requires all successors to accept; Q⊕
  (existential) requires at least one.  Polynomial transition coefficients
  weight each branch's cost, enabling weighted game-theoretic analysis
  over the alternating structure.
- Quantifier evaluation maps `forall` to Q⊗  and `exists` to Q⊕.
  Process bisimulation checks require alternating moves (e.g., Rholang
  "for every send in A, exists a matching receive in B").  Parse
  disambiguation models ambiguity as a game between existential (parser
  chooses rule) and universal (input chooses token) players — acceptance
  determines whether a disambiguation strategy exists.
- N06 flags provably non-bisimilar state pairs in the polynomial
  transition system; N07 flags significant Q⊗/Q⊕  degree asymmetry
  (imbalanced game structure).
- `analyze_from_bundle()` produces `AlternatingAnalysis` (branching
  statistics, polynomial data) wired into `LintContext.alternating_result`.
  Activated by universal quantifiers (`ForallFinite`, `ForallInfinite`)
  in predicate dispatch (estimated cost = 3).

**Lints:** N06 polynomial ISO anomalies, N07 branching imbalance.

### 7.6 M4: Weighted Visibly Pushdown Automata (VPA)

**Source:** `vpa.rs` (feature: `vpa`)

**Theory:** VPAs partition the input alphabet into call (push), return (pop),
and internal symbols (Alur & Madhusudan 2004).  This visible nesting structure
makes language equivalence and inclusion decidable — unlike general pushdown
automata.

**Key type:**

```rust
struct WeightedVpa<W: Semiring> {
    alphabet: VpaAlphabet,  // call_symbols, return_symbols, internal_symbols
    call_transitions: HashMap<(State, CallSym), Vec<(Target, StackPush, W)>>,
    return_transitions: HashMap<(State, RetSym, StackTop), Vec<(Target, W)>>,
    internal_transitions: HashMap<(State, IntSym), Vec<(Target, W)>>,
}
```

**Operations:** `check_equivalence()`, `complement()`, `intersect()`,
`build_alphabet_from_syntax()`.

**Pipeline integration:** `build_alphabet_from_syntax()` derives the
alphabet partition from grammar rules.  Bracket tokens (`(`, `)`, `{`, `}`,
`[`, `]`) are classified as call/return; all others as internal.  Results
feed V01-V06 lints including determinization opportunities and nesting
bound analysis.

**VPA nesting bound:** When `vpa_max_nesting_bound` is computed, it provides
an upper bound on bracket depth.  This bound feeds into:
- Recovery: `vpa_nesting_ceiling` in `RecoveryConfig`
- Parser: stack depth pre-allocation hints
- Lint V06: stack alphabet optimization suggestions

**Applications:**
- `check_equivalence()` detects redundant bracket rules;
  `complement()` generates counterexample inputs for failing inclusion
  checks; `intersect()` computes shared nesting structures.
  `build_alphabet_from_syntax()` derives the call/return/internal
  partition from grammar rules automatically.
- Bracket tokens (`(`, `)`, `{`, `}`, `[`, `]`) partition into
  call/return symbols.  Scope analysis verifies name references fall
  within enclosing binders (e.g., Rholang `new x in { P }`), quantifier
  nesting is well-formed, and suffix language analysis determines whether
  more input is needed to close open brackets.
- `vpa_max_nesting_bound` feeds `RecoveryConfig.vpa_nesting_ceiling`
  (bracket-mismatch repair cost scaling) and trampoline parser stack
  pre-allocation, avoiding dynamic resizing for well-bounded grammars.
- V05 flags exponential determinization blowup (too many stack symbols);
  V06 suggests stack alphabet simplification.
- `analyze_from_bundle()` produces `VpaAnalysis` (nesting bound,
  alphabet partition, determinization feasibility) wired into
  `LintContext.vpa_result`.

**Lints:** V01-V06.

### 7.7 M5: Parity Alternating Tree Automata (PATA)

**Source:** `parity_tree.rs` (feature: `parity-tree-automata`)

**Theory:** PATA verify properties of tree-structured data (ASTs) via the
mu-calculus (Emerson & Jutla 1991).  The parity acceptance condition ensures
decidability via reduction to parity games.

**Parity condition:** A run is accepting if the minimum priority visited
infinitely often along every path is even.

**Key algorithm:** Zielonka solver — recursive attractor computation over
parity games, computing winning regions for existential and universal players.

**Operations:** `check_emptiness()` (Zielonka), `mu_calculus_to_pata()`,
`check_inclusion()`, `evaluate_term()`.

**Applications:**
- `mu_calculus_to_pata()` compiles mu-calculus formulas to PATA.  The
  Zielonka solver decides emptiness via recursive attractor computation
  over parity games.  `evaluate_term()` runs the PATA bottom-up over a
  parsed AST to verify structural invariants (e.g., "every `if` node
  has exactly 3 children").  Emptiness witnesses provide concrete AST
  counterexamples for diagnostic messages.
- Recursive property verification over tree-structured data: type
  specifications with mutually recursive definitions (e.g., MeTTa nested
  function applications), safety properties over self-replicating
  processes (e.g., Rholang `*ch!(*ch)` unbounded-resource checks), and
  post-parse AST well-formedness validation.
- PT01 flags empty PATA languages (vacuously true or contradictory
  spec); PT02 identifies zero-state priority levels (simplifiable
  acceptance conditions); PT03 flags deep priority nesting (high
  Zielonka solver cost, potentially reformulable with fewer alternating
  fixpoints).
- `analyze_from_bundle()` produces `ParityTreeAnalysis` (emptiness
  verdicts, priority distribution) wired into
  `LintContext.parity_tree_result`.  Activated by fixpoint relations
  (`letprop`, `mu`, `nu`) in predicate dispatch (estimated cost = 4).

**Lints:** PT01-PT03.

### 7.8 M6: Register Automata

**Source:** `register_automata.rs` (feature: `register-automata`)

**Theory:** Register automata extend finite automata with a finite number of
registers that can store values from an unbounded data domain (Kaminski &
Francez 1994).  Transitions can test equality between the current input and
register contents, and can store new values.

**Register operations:**
- `Store(register_id)` — save current input value
- `TestEq(register_id)` — check equality with stored value
- `TestFresh` — verify value differs from all stored values

**Applications:**
- `Store(r)` saves the current input value; `TestEq(r)` checks equality
  with a stored value; `TestFresh` verifies the input differs from all
  stored values.  These operations track data dependencies across
  derivations without enumerating the unbounded data domain.
- Structural correspondence enforcement (open/close tag matching),
  name freshness (e.g., Rholang `new x in {}` capture-avoidance), data
  equality guards (register tracks most recent value, accepts on match),
  and variable binding consistency (e.g., MeTTa `(foo $x $y) -> (bar
  $x $x)` verifies both RHS `$x` reference the same captured value).
- RA01 flags `TestEq(r)` on an uninitialized register (use-before-
  definition); RA02 flags stored-but-never-tested registers (redundant
  `Store`); RA03 flags all-dead registers (DFA degeneration, no
  data-aware analysis needed).
- `analyze_from_bundle()` produces `RegisterAnalysis` (per-register
  usage tracking) wired into `LintContext.register_result`.  Activated
  by equality relations (`eq`, `neq`, `==`, `!=`, `fresh`) in predicate
  dispatch (estimated cost = 2).

**Lints:** RA01 unbound-data, RA02 redundant-register, RA03 register-equivalence.

### 7.9 M7: Probabilistic Automata

**Source:** `probabilistic.rs` (feature: `probabilistic`)

**Theory:** Probabilistic automata assign transition probabilities
(as LogWeight for numerical stability) and enable statistical disambiguation
via forward, Viterbi, and Baum-Welch algorithms (Rabiner 1989).

**Key algorithms:**
- `probability_of()` — forward algorithm (sum-product over all paths)
- `viterbi()` — most-probable path (max-plus)
- `entropy()` — per-state Shannon entropy via expectation semiring
- `train_from_corpus()` — Baum-Welch EM for parameter estimation

**Semiring interaction:** LogWeight provides numerical stability for
probability operations.  The forward algorithm uses LogWeight's `plus` =
log-sum-exp (numerically stable probability summation) and `times` =
addition (log-probability accumulation):

```
Forward pass:   α[j] = ⊕_{i→j} α[i] ⊗  w(i,j)
                     = -ln(Σᵢ exp(-α[i]) · exp(-w(i,j)))

Viterbi pass:   v[j] = min_{i→j} v[i] + w(i,j)    (TropicalWeight)

Baum-Welch:     ξ(i,j) = α[i] ⊗  w(i,j) ⊗  β[j] ⊘ α[final]
                (per-transition expected count for parameter re-estimation)
```

**Applications:**
- `probability_of()` computes the forward algorithm (LogWeight
  sum-product over all paths).  `viterbi()` finds the most-probable
  path (max-plus).  `entropy()` computes per-state Shannon entropy.
  `train_from_corpus()` runs Baum-Welch EM parameter estimation,
  learning transition probabilities from sample inputs without manual
  weight tuning.
- Corpus-trained weights resolve parse ambiguity (multiple rules on the
  same prefix), rank completion suggestions by likelihood (Viterbi
  decoding on partial input), and order dispatch by expected frequency
  (e.g., Rholang multi-pattern channel matching).  Per-state entropy
  analysis identifies high-entropy dispatch points that benefit most
  from guard reordering.
- PR01 flags low-selectivity rules (dead-rule or reordering candidates);
  PR02 flags non-stochastic states (outgoing weights not summing to 1);
  PR03 flags high-entropy dispatch; PR04 flags expected-depth anomalies.
- `analyze_from_bundle()` produces `ProbabilisticAnalysis` (per-state
  entropy, selectivity, stochasticity) wired into
  `LintContext.probabilistic_result`.  Activated by ≥2 channel
  references in predicate dispatch (estimated cost = 5).

**Lints:** PR01 low-selectivity, PR02 non-stochastic, PR03 high-entropy,
PR04 expected-depth anomaly.

### 7.10 M8: Multi-Tape Automata

**Source:** `multi_tape.rs` (feature: `multi-tape`)

**Theory:** K-tape automata process K synchronized input streams
simultaneously (Kempe 2004).  Transitions consume a K-tuple of symbols
(with optional epsilon on individual tapes).

**Operations:**
- `pair()` — combine two single-tape automata into 2-tape product
- `auto_intersect(i, j)` — constraint: tapes i and j must match
- `project(tape_idx)` — extract single-tape behavior
- `evaluate()` — BFS over (state, positions_per_tape)

**Applications:**
- `pair()` combines two single-tape automata into a 2-tape product.
  `auto_intersect(i, j)` constrains tapes i and j to produce matching
  labels (equality at the automaton level).  `project(tape_idx)` extracts
  single-tape behavior for independent analysis.  `evaluate()` performs
  BFS over (state, positions_per_tape) tuples for full K-tape simulation.
- Multi-channel synchronized consumption maps each channel to a tape
  (e.g., Rholang `for (@x <- ch1, @y <- ch2)`).  Cross-tape predicates
  encode relational constraints between channels.  Multi-argument type
  verification proceeds simultaneously via K-tape product construction.
- MT01 flags overlapping tape labels (ambiguous synchronized consumption);
  MT02 flags disconnected tapes (decomposable to cheaper single-tape
  analyses).
- `analyze_from_bundle()` produces `MultiTapeAnalysis` (tape connectivity,
  label overlap) wired into `LintContext.multi_tape_result`.  Activated
  by cross-channel references or ≥2 distinct channels in predicate
  dispatch (estimated cost = 5).

**Lints:** MT01 channel-overlap, MT02 disconnected tapes.

### 7.11 M9: Multiset Automata

**Source:** `multiset_automata.rs` (feature: `multiset-automata`)

**Theory:** Multiset automata track feature multiplicities via the featured
multiset semiring (Muller, Weiss, & Lochau 2024).  Features map to grammar
constructs (operator occurrences, nesting depth), and cardinality constraints
enforce well-formedness.

**Semirings:** `MultisetWeight` (ℕ₀^F, pointwise max/add) and
`TropicalMultisetWeight` (ℝ₊^F∞, pointwise min/add) — both `HeapSemiring`
(non-Copy, HashMap-backed).

**Operations:** `multiplicity_of()`, `satisfies_cardinality()`,
`tropical_projection()`.

**Applications:**
- `multiplicity_of()` tracks per-feature counts.
  `satisfies_cardinality()` verifies multiplicity constraints.
  `tropical_projection()` maps `MultisetWeight` (ℕ₀^F) to
  `TropicalMultisetWeight` (ℝ₊^F∞) — the tropical variant is decidable,
  enabling tractable cardinality analysis when full multiset reasoning
  is too expensive.
- Parallel composition multiplicities (e.g., Rholang `{ P | Q | Q }`
  tracking "exactly two copies of Q"), cardinality guards, collection
  decomposition (`*sep`/`*map`/`*zip` multiplicity bounds), and
  reaction-rule conservation laws (MeTTa chemical abstract machine
  semantics — total multiplicity invariants across rewrites).
- MS01 flags unsatisfiable cardinality constraints (e.g.,
  `count(ch) >= 5 /\ count(ch) <= 2`); MS02 flags always-true
  (redundant) feature checks.
- `analyze_from_bundle()` produces `MultisetAnalysisResult` (per-feature
  multiplicity) wired into `LintContext.multiset_result`.  Both semirings
  are `HeapSemiring` (non-Copy, HashMap-backed).  Activated by
  cardinality relations (`count`, `size`, `>=`, `<=`) in predicate
  dispatch (estimated cost = 2).

**Lints:** MS01 unsatisfiable-constraint, MS02 redundant-check.

### 7.12 M10: Weighted MSO

**Source:** `weighted_mso.rs` (feature: `weighted-mso`)

**Theory:** Weighted Monadic Second-Order logic provides the specification
language for grammar properties (Droste & Gastin 2007).  The Buchi-Elgot-
Trakhtenbrot theorem establishes equivalence between recognizable formal
power series (WFSA) and definable restricted MSO sentences.

**Formula classification:**

| Class       | Quantifiers          | Decidable   |
|-------------|----------------------|-------------|
| FirstOrder  | no set quantifiers   | ✓           |
| Existential | ∃X only              | ✓           |
| Restricted  | no ∀X, restricted ∀x | ✓           |
| Full        | ∀X, ∃X unrestricted  | undecidable |

**Applications:**
- `classify_formula()` partitions formulas into FirstOrder, Existential,
  Restricted (all decidable), and Full (undecidable).
  `check_decidability()` determines compilability.
  `evaluate_sentence_bool()` directly evaluates decidable formulas.
  The Buchi-Elgot-Trakhtenbrot theorem guarantees an equivalent weighted
  automaton exists for the restricted fragment.
- Guard specifications compile as weighted MSO formulas (e.g.,
  `forall y. (reachable(x,y) => safe(y))`).  Recognizable properties of
  token sequences (e.g., "every open bracket is eventually closed") and
  channel protocols (e.g., Rholang send-receive matching) are compilable
  when they fall in the restricted fragment.
- MSO01 flags unrestricted ∀X quantifiers (undecidable Full class);
  MSO02 flags non-recognizable formula steps (incompilable subformulas);
  MSO03 identifies semantically equivalent formula pairs (simplification
  opportunity).
- Always-on as BASE dispatch bit 9.  `analyze_from_bundle()` produces
  `MsoAnalysis` (formula classifications) wired into
  `LintContext.mso_result`.

**Lints:** MSO01 unrestricted-universal, MSO02 non-recognizable-step,
MSO03 equivalent-formulas.

### 7.13 M11: Two-Way Transducers

**Source:** `two_way_transducer.rs` (feature: `two-way-transducer`)

**Theory:** Two-way transducers can move the read head both left and right
(Feng & Maletti 2022).  States are partitioned into forward (Q→, moves
right) and backward (Q←, moves left) sets.

**Applications:**
- States partition into Q→ (forward, moves right) and Q← (backward,
  moves left).  Backward-propagation computes pre-images of cross-channel
  constraints, narrowing receiver sets at receive time (e.g., Rholang
  `for (@x <- ch1, @y <- ch2)` determines which ch1 values are relevant
  given ch2's constraints, discarding non-participating messages).
- Cross-channel constraint propagation derives constraints between
  channels (e.g., `y == g(x)` propagates a derived constraint back onto
  ch1).  `TwoWayAnalysis` tracks `num_forward` and `num_backward` states
  separately, enabling cost-benefit analysis of bidirectional vs.
  one-way evaluation.
- TW01 flags circular channel dependencies (Tarjan SCC on the dependency
  graph — deadlocking join patterns); TW02 flags one-way sufficiency
  (no Q← states needed, cheaper transducer suffices); TW03 flags
  divergent backward propagation (oscillation without fixpoint).
- `analyze_from_bundle()` produces `TwoWayAnalysis` (forward/backward
  state counts, channel dependency graph) wired into
  `LintContext.two_way_result`.  Activated by cross-channel references
  in predicate dispatch (highest estimated cost = 6).

**Lints:** TW01 circular-dependency, TW02 one-way-sufficient,
TW03 constraint-divergent.

### 7.14 Predicate Dispatch Controller

**Source:** `predicate_dispatch.rs` (feature: `predicate-dispatch`)

**Theory:** The predicate dispatch module uses Eilenberg variety
classification (Eilenberg 1976) to determine the minimal set of advanced
automata modules needed for each grammar category.

**Signature:** An 11-bit `PredicateSignature(u16)` encodes module activation:

| Bit | Module         | Bit | Module           |
|-----|----------------|-----|------------------|
| 0   | M1 Symbolic    | 6   | M7 Probabilistic |
| 1   | M2 Buchi       | 7   | M8 Multi-Tape    |
| 2   | M3 AWA         | 8   | M9 Multiset      |
| 3   | M4 VPA         | 9   | M10 MSO          |
| 4   | M5 Parity Tree | 10  | M11 Two-Way      |
| 5   | M6 Register    |     |                  |

**Base activation:** M1 (Symbolic) + M10 (MSO) are always active when
predicate dispatch is enabled.  Advanced modules are activated on demand
based on guard complexity: relational predicates activate VPA/Buchi,
quantifiers activate Parity Tree, data equality activates Register, etc.

**Key function:**

```rust
fn extract_features(expr: &PredicateExpr, ctx: &ChannelContext)
    -> PredicateProfile
```

O(|AST|) feature extraction from guard expressions determines which
`ModuleId` values are needed.

**Applications:**
- `extract_features()` inspects the guard AST in O(|AST|), producing a
  `PredicateProfile` that maps to an 11-bit `PredicateSignature(u16)`.
  A guard like `x == fresh_name /\ count(ch) >= 2` activates only
  M1+M6+M9+M10, skipping 7 modules.  Ground-decidable guards (e.g.,
  `x > 5`) activate only the BASE signature (M1+M10), enabling T1
  static elimination without heavyweight analyses.
- `classify_grammar()` orders module execution by `estimated_cost()`
  (M1/M10 = 1, M6/M9 = 2, M2/M3 = 3, M4/M5 = 4, M7/M8 = 5, M11 = 6),
  enabling early termination when cheaper analyses already resolve the
  property.  The controller automatically determines the minimal module
  set from the guard AST (e.g., Rholang `new x in { for (...) }` with
  cross-channel `x` triggers M6+M8+M11).
- PD01 flags degenerate (BASE-only) signatures; PD02 flags
  all-modules-activated (no dispatch savings); PD03 reports per-predicate
  module-skip savings; PD04 flags cross-channel references compiled
  without the `two-way-transducer` feature gate.
- `classify_grammar()` runs in Phase 7A, producing a
  `GrammarDispatchPlan`.  Each Phase 7B thread checks
  `dispatch_plan.requires(ModuleId)` — modules not in the signature are
  skipped entirely.

**Lints:** PD01 degenerate-predicate, PD02 all-modules-activated,
PD03 dispatch-savings, PD04 missing-feature-gate.

---

## 8. Mathematical Analysis Modules

PraTTaIL includes 14 mathematical analysis modules organized in a layered
verification stack.

### 8.1 Layered Verification Stack

```
┌─────────────────────────────────────────────────────────┐
│  Meta-Level (KAT, Morphism, Proof Output)               │
│  Kleene algebra equivalence, theory morphisms, certs    │
├─────────────────────────────────────────────────────────┤
│  Temporal (LTL, Provenance, CRA)                        │
│  LTL model checking, derivation tracking, streaming     │
├─────────────────────────────────────────────────────────┤
│  Concurrency (Petri, Nominal, Alternating)              │
│  Deadlock, fresh names, bisimulation games              │
├─────────────────────────────────────────────────────────┤
│  Pushdown (WPDS, EWPDS, VPA, Safety, CEGAR)             │
│  Stack-aware reachability, counterexample refinement    │
├─────────────────────────────────────────────────────────┤
│  Tree / Semantic (WTA, Confluence, Termination)         │
│  AST verification, critical pairs, dependency pairs     │
├─────────────────────────────────────────────────────────┤
│  String / Basic (Algebraic, Newton, Forward-Backward)   │
│  Path expressions, fixpoint acceleration, scoring       │
├─────────────────────────────────────────────────────────┤
│  Semiring Layer (shared by ALL levels)                  │
│  20 semiring types, StarSemiring, matrix_star()         │
└─────────────────────────────────────────────────────────┘
```

### 8.2 Feature Matrix 4: Analysis Module Capabilities

| Module           | Feature      | Theory              | What It Checks            | Output                           |
|------------------|--------------|---------------------|---------------------------|----------------------------------|
| confluence       | trs-analysis | Knuth-Bendix        | Critical pair joinability | ConfluenceAnalysis               |
| termination      | trs-analysis | Dependency pairs    | TRS termination via SCC   | TerminationResult                |
| algebraic        | (always on)  | Tarjan path expr.   | Interprocedural analysis  | PathExpr\<W\>, AlgebraicAnalysis |
| newton           | (always on)  | Newton fixpoint     | Faster Kleene iteration   | Vec\<W\> fixpoint values         |
| forward_backward | (always on)  | FB algorithm        | Path scoring in DAGs      | HotPathReport\<W\>               |
| kat              | kat          | KAT equivalence     | Parser control flow       | Hoare triple verification        |
| verify           | (always on)  | WPDS prestar        | Safety/liveness           | SafetyResult\<W\>, Verdict       |
| cegar            | (always on)  | CEGAR loop          | Abstraction refinement    | Boolean→Counting→Tropical        |
| petri            | petri        | Karp-Miller         | Deadlock, boundedness     | CoverabilityResult               |
| nominal          | nominal      | Orbit-finite        | Name-binding safety       | alpha-equivalence check          |
| cra              | cra          | CRA streaming       | Register quantitative     | CraAnalysis                      |
| morphism         | morphisms    | Theory morphisms    | Structure preservation    | TheoryMorphism                   |
| proof_output     | proofs       | Certificates        | Layered proof output      | ProofOutput (human + Rocq)       |
| provenance       | provenance   | How-provenance N[X] | Derivation tracking       | ProvenanceWeight                 |

### 8.3 TRS Analysis (Confluence and Termination)

**Source:** `confluence.rs`, `termination.rs` (feature: `trs-analysis`)

**Confluence** (Knuth & Bendix 1970): Detects critical pairs — overlapping
rule positions where two different rewrites apply.  Each pair is tested for
joinability (do both sides reduce to the same normal form?).

**Key types:**

```rust
enum Term {
    Var(String),
    App { symbol: String, args: Vec<Term> },
}

struct CriticalPair {
    left: Term,                // rewriting with rule 1
    right: Term,               // rewriting with rule 2
    overlap_position: Vec<usize>, // where rules overlap
}

struct ConfluenceAnalysis {
    is_confluent: bool,
    critical_pairs: Vec<CriticalPair>,
    joinable_count: usize,
    non_joinable_count: usize,
}
```

**Pipeline integration:** `syntax_to_rewrite_rules()` converts grammar
equations and rewrites to `RewriteRule` values.  Results feed T01-T02 lints
and repair suggestions via `enrich_diagnostics_with_repairs()`.

**Termination** (Arts & Giesl 2000): Extracts dependency pairs, builds the
dependency graph, computes SCCs via Tarjan's algorithm, and verifies
structural decrease on argument positions within each SCC.

**Key types:**

```rust
struct DependencyPair {
    source: Term,         // marked LHS
    target: Term,         // marked RHS subterm
    rule_origin: usize,   // which rewrite rule
}

enum TerminationResult {
    Terminating,
    PotentiallyNonTerminating,
    Unknown,
}
```

**Algorithm:** For each SCC in the dependency graph, check that at least one
argument position has strict decrease and the rest have weak decrease.  If
all SCCs pass, the system is terminating.

**Applications:**
- `syntax_to_rewrite_rules()` converts grammar `equations {}` and
  `rewrites {}` to TRS.  `check_confluence()` detects critical pairs
  (overlapping rule positions) and tests joinability.  Dependency pair
  analysis with Tarjan SCC decomposition verifies termination — each SCC
  must exhibit structural decrease in at least one argument position.
- Rewrite rule determinism: bidirectional equations require joinable
  critical pairs for equality saturation soundness (e.g., MeTTa e-graph
  correctness), structural congruence rules require confluence for
  deterministic reduction (e.g., Rholang `Comm`/`ParCong`/`NewCong`),
  and directed rewrites (`~>`) require termination to prevent normalizer
  divergence.
- T01 flags non-confluence with witness critical pairs; T02 flags
  non-termination with dependency cycles; T03/T04 report successful
  verification.  Non-joinable pairs generate `RepairSuggestion` entries
  identifying conflicting rules and overlap positions.
- `TrsConfluenceCheck` in cost-benefit gates exhaustive vs. sampled
  analysis by grammar size.  `analyze_from_bundle()` returns
  `ConfluenceAnalysis` + `TerminationResult`.

### 8.4 Algebraic Program Analysis

**Source:** `algebraic.rs`, `newton.rs` (always on)

Tarjan's path expression algorithm (Tarjan 1981) computes the regular
expression of paths through a control-flow graph, then evaluates the
expression in any `StarSemiring`.

**Key types:**

```rust
enum PathExpr<W> {
    Atom(W),         // single edge weight
    Seq(Box, Box),   // sequential composition: ⊗
    Alt(Box, Box),   // alternative: ⊕
    Star(Box),       // Kleene closure: *
    Zero,            // empty (0̄)
    One,             // identity (1̄)
}
```

Evaluation: `Atom(w) → w`, `Seq(a,b) → a ⊗  b`, `Alt(a,b) → a ⊕  b`,
`Star(a) → a.star()`.

**Newton's method** (Esparza et al. 2010) accelerates fixpoint computation
for omega-continuous semirings: ν₀ = 0̄, νᵢ₊₁ = J_F(νᵢ)* ⊗  F(νᵢ).
For idempotent semirings, convergence is guaranteed in at most h+1 iterations
where h is the Strahler number of the equation system.

**Applications:**
- Tarjan path expressions summarize CFG (control-flow graph) paths into `PathExpr<W>`.
  `PathExpr::evaluate()` interprets in any `StarSemiring` —
  `TropicalWeight` (shortest-path), `LogWeight` (log-probability),
  `BooleanWeight` (reachability), `CountingWeight` (path counting) —
  one analysis, four answers.  `matrix_star()` (generalized
  Floyd-Warshall) computes all-pairs closure, providing complete
  reachability information for downstream modules (verify, cegar).
- `newton_fixpoint()` solves grammar equation systems in h+1 iterations
  (h = Strahler height) for idempotent semirings, vs. potentially
  unbounded naive Kleene iteration.  Path expressions over `LogWeight`
  compute total communication-path probability (e.g., Rholang protocol
  coverage analysis).
- `build_cfg()` extracts a control-flow graph from the WPDS;
  `tarjan_decompose()` identifies DAG + cycle-nest regions;
  `path_expression()` computes the regular expression over all paths.
- Both modules are always-on (no feature gate).
  `analyze_from_bundle()` and `accelerate_from_bundle()` provide bridge
  functions wired through `MathAnalysisResults`.

### 8.5 Forward-Backward Algorithm

**Source:** `forward_backward.rs` (always on)

Semiring-generic path scoring over DAGs:

| Semiring       | Forward computes        | Backward computes       |
|----------------|-------------------------|-------------------------|
| TropicalWeight | Shortest path (Viterbi) | Reverse shortest path   |
| LogWeight      | Log-probability         | Reverse log-probability |
| BooleanWeight  | Reachability            | Reverse reachability    |
| CountingWeight | Path count              | Reverse path count      |

**Hot-path analysis:** `expected_weight(u,v) = α(u) ⊗  w(u,v) ⊗  β(v)` ranks
edges by their contribution to the total weight.

**Key types:**

```rust
struct RankedEdge<W: Semiring> {
    from: usize,
    to: usize,
    weight: W,              // original edge weight
    expected_weight: W,     // α(from) ⊗  weight ⊗  β(to)
}

struct HotPathReport<W: Semiring> {
    ranked_edges: Vec<RankedEdge<W>>,  // sorted by expected weight
    total: W,                           // partition function
    num_nodes: usize,
    num_edges: usize,
}
```

**Pipeline integration (Phase 5B.5):** Hot-path identification feeds
trampoline codegen — hot edges get `#[inline]` annotations, cold edges
get `#[cold]` to improve instruction cache locality.

**Applications:**
- `hot_path_analysis()` ranks edges by `expected_weight = α(u) ⊗  w(u,v)
  ⊗  β(v)`.  `critical_path()` extracts the single highest-weight path.
  `edge_occupancy()` normalizes per-edge contributions against
  `total_weight()` (partition function).  Semiring-generic:
  `TropicalWeight` → shortest path, `LogWeight` → log-probability,
  `BooleanWeight` → reachability, `CountingWeight` → path count.
- `HotPathReport<W>` feeds trampoline codegen (hot edges → `#[inline]`,
  cold → `#[cold]` for instruction cache locality) and recovery
  heuristics (high-traffic repairs weighted as more likely correct).
  `edge_occupancy()` with `LogWeight` reveals frequently exercised
  grammar rules (e.g., Rholang channel dispatch profiling).
- Always-on (no feature gate).  Forward scores α(u) and backward scores
  β(v) combine per-edge to produce the ranked `HotPathReport<W>`
  consumed by codegen and recovery.  Results also feed WFST weight
  training when `wfst-log` is enabled.

### 8.6 KAT (Kleene Algebra with Tests)

**Source:** `kat.rs` (feature: `kat`)

**Theory:** KAT (Kozen 1997) extends Kleene algebra with Boolean tests,
providing a decidable equational theory for parser control-flow verification.

```rust
enum KatExpr {
    Zero, One,
    Test(BooleanTest),        // Boolean guard
    Action(String),           // atomic action (token consumption)
    Seq(Box, Box),            // sequential composition
    Alt(Box, Box),            // choice
    Star(Box),                // iteration
}
```

**Hoare triple verification:** `{b} p {c}` ≡ `b · p · ¬c = 0` — the program
`p`, starting in states satisfying `b`, never reaches states violating `c`.

**Algorithm:** Bounded Brzozowski derivative computation: enumerate all Boolean
valuations, compute symbolic derivatives, check nullable equivalence.

**Hoare triple verification detail:**

```
Given {b} p {c}:
  Compute: b · p · ¬c
  Simplify using KAT algebraic identities:
    0 · x = 0,  x · 0 = 0     (zero annihilation)
    1 · x = x,  x · 1 = x     (identity)
    b · b = b                   (test idempotence)
    b · ¬b = 0                  (test complement)
    x + x = x                   (idempotence)
  If result = 0: triple verified
  Else: triple violated (counterexample exists)
```

**Pipeline integration:** Maps parse flow to KAT expressions:
- `Seq` = chaining (sequential parse steps)
- `Alt` = dispatch (token-based choice)
- `Star` = recursion (grammar cycle)
- Tests = token guards (`is_token("+")`, `has_remaining()`)

**Applications:**
- Hoare triple `{b} p {c}` verified via `b · p · ¬c = 0`.  Bounded
  Brzozowski derivative computation enumerates Boolean valuations and
  checks nullable equivalence.  Parse control flow maps to `Seq`
  (chaining), `Alt` (dispatch), `Star` (recursion), `Test` (token
  guards like `is_token("+")`, `has_remaining()`).
- Parser correctness contracts (`{valid_input} parse_expr
  {ast_well_formed}`), refactoring equivalence (`parse_v1 ≡_KAT
  parse_v2`), normalizer idempotence (`normalize; normalize ≡_KAT
  normalize`), and type safety preservation (e.g., Rholang
  `{well_typed(P)} reduce {well_typed(Q)}`).
- K01 flags semantically different parse paths (regression indicator);
  K02 flags equivalent paths (simplification opportunity — distinct
  grammar constructs with identical KAT semantics).
- `check_from_bundle()` maps WPDS analysis and grammar syntax into
  `KatExpr`.  `check_equivalence_bounded()` uses configurable depth
  limit, trading completeness for performance on large expressions.

**Lints:** K01 kat-inequivalence, K02 kat-equivalent.

### 8.7 Verify Module (Safety & Liveness)

**Source:** `verify.rs` (always on)

The verify module uses WPDS-based reachability to check safety and liveness
properties, producing structured repair suggestions when violations are found.

**Key types:**

```rust
struct SafetyResult<W: Semiring> {
    safe: bool,
    initial_weight: W,
    witness_trace: Vec<StackSymbol>,
}

enum Verdict {
    Verified,    // property holds
    Violated,    // property fails with witness
    Unknown,     // analysis inconclusive
}

struct VerificationResult<W: Semiring> {
    verdict: Verdict,
    property: String,
    weight: W,
    witness: Vec<StackSymbol>,
}
```

**Algorithm:** `check_safety()` builds a P-automaton accepting bad stack
configurations, runs `prestar` to propagate backward, then checks if the
initial configuration intersects the result.

**Repair suggestions:**
- Per-step guards (increasing cost by trace position)
- Restrict-initial (cost 3, confidence 0.5)
- Invariant strengthening (confidence 0.7)
- Postcondition weakening (confidence 0.6)

**Applications:**
- `check_safety()` builds a P-automaton accepting bad stack
  configurations, runs `prestar` backward, and checks initial
  configuration intersection.  `extract_witness_trace()` produces
  the exact stack-operation sequence reaching the violation.
  Semiring-generic: `BooleanWeight` → yes/no reachability,
  `TropicalWeight` → minimum cost to bad state, `CountingWeight` →
  path count.
- Parser deadlock-freedom (no stuck configurations), communication
  safety (e.g., Rholang unmatched send/blocked receive detection),
  and guard completeness (every input on a channel matches at least
  one guard — incomplete pattern match detection).
- `suggest_safety_repairs()` generates ranked suggestions: per-step
  guards (increasing cost by trace position), restrict-initial (cost 3,
  confidence 0.5), invariant strengthening (confidence 0.7),
  postcondition weakening (confidence 0.6).
- `SafetyVerification` in cost-benefit gates `prestar` by WPDS size.
  `verify_from_bundle()` produces `SafetyResult<BooleanWeight>` with
  verdict, initial weight, and witness trace, wired through
  `MathAnalysisResults`.

### 8.8 Safety Verification via WPDS and CEGAR

**Source:** `cegar.rs` (always on)

Safety verification uses `prestar` to backward-propagate bad states through
the WPDS.  If the initial configuration intersects the prestar result, a
safety violation is reported with a witness trace.

**CEGAR loop** (counterexample-guided abstraction refinement): Iteratively
refines the abstraction when the initial check is inconclusive:

```
┌──────────────────────────────────────────────────────────────────┐
│                          CEGAR Loop                              │
│                                                                  │
│  Abstraction ladder: Boolean ──→ Counting ──→ Tropical           │
│                      (coarse)    (medium)     (precise)          │
│                                                                  │
│         ┌─────────────────────────────────────────┐              │
│         │                                         │              │
│         ▼                                         │              │
│  ┌──────────────────────────────┐                 │              │
│  │ Project WPDS to level L      │                 │              │
│  └──────────────┬───────────────┘                 │              │
│                 ▼                                 │              │
│  ┌──────────────────────────────┐                 │              │
│  │ prestar(abstract WPDS, bad)  │                 │              │
│  └──────────────┬───────────────┘                 │              │
│                 ▼                                 │              │
│        ∩ initial = ∅?                             │              │
│         ╱            ╲                            │              │
│       yes             no                          │              │
│        │          (counterexample)                │              │
│        ▼               ▼                          │              │
│     ┌──────┐  validate trace in                   │              │
│     │ SAFE │  concrete model                      │              │
│     └──────┘       ╱          ╲                   │              │
│               spurious      genuine               │              │
│                   │            │                  │              │
│                   │            ▼                  │              │
│                   │      ┌───────────┐            │              │
│                   │      │ VIOLATION │            │              │
│                   │      │ (witness) │            │              │
│                   │      └───────────┘            │              │
│                   ▼                               │              │
│            L < Tropical?                          │              │
│             ╱         ╲                           │              │
│           yes          no                         │              │
│            │       (most precise ──→ VIOLATION)   │              │
│            │                                      │              │
│       L := next(L) ───────────────────────────────┘              │
│                                                                  │
│  Termination: at most 3 iterations (Boolean → Counting →         │
│  Tropical).  Tropical is the identity projection — no spurious   │
│  counterexamples possible.                                       │
│                                                                  │
└──────────────────────────────────────────────────────────────────┘
```

Each level adds precision at the cost of computational effort. The loop
starts at the coarsest abstraction (Boolean) and refines only when a
spurious counterexample is found, avoiding the expense of exact analysis
for properties verifiable cheaply. The back-edge from `L := next(L)`
to `Project WPDS` is the key CEGAR structure — it is a genuine loop,
not a linear cascade.

**Applications:**
- Abstraction ladder Boolean→Counting→Tropical (at most 3 iterations).
  Each level projects the WPDS, runs `prestar(abstract WPDS, bad)`, and
  validates traces against the concrete model.  Tropical is the identity
  projection — no spurious counterexamples at the final level.  Tier
  mapping: Boolean ↔ T1, Counting ↔ T2, Tropical ↔ T3, timeout ↔ T4.
- Grammar safety verification starts at Boolean (O(|rules|)), refining
  only on spurious counterexamples (e.g., Rholang parallel composition
  deadlock over-approximation).  Each refinement level eliminates
  counterexamples that existed in the coarser abstraction but not in
  the finer one.
- S01 safety-violation; S02 safety-verified; S03 per-level iteration
  progress; S04 converged; S05 timeout; S06 invariant suggestion
  (refined abstraction as candidate invariant).
- `CegarRefinement` in cost-benefit gates refinement by WPDS complexity.
  `cegar_from_bundle()` runs the loop, returning per-level verdicts.

**Lints:** S01 safety-violation, S02 safety-verified, S03 CEGAR-iteration,
S04 CEGAR-converged, S05 CEGAR-timeout, S06 invariant-suggestion.

### 8.9 Petri Nets (Concurrency Analysis)

**Source:** `petri.rs` (feature: `petri`)

**Theory:** Petri nets model concurrent systems as places (resources) and
transitions (actions) (Karp & Miller 1969).  PraTTaIL maps grammar concurrency
constructs to places and transitions.

**Key operations:**
- `check_coverability()` — Karp-Miller tree (EXPSPACE)
- `check_deadlock()` — no enabled transitions from some reachable marking
- `check_boundedness()` — all places ≤ k tokens in all reachable markings

**Applications:**
- `check_coverability()` constructs a Karp-Miller tree (EXPSPACE) to
  verify that no place accumulates unbounded tokens.
  `check_deadlock()` identifies markings where no transition is enabled
  (mutual waiting).  `check_independence()` verifies two transitions
  can fire concurrently without shared-place interference.  Grammar
  concurrency constructs map to places (channels/tokens) and transitions
  (processes/rewrites), enabling analysis of parallel composition
  (e.g., Rholang `{ P | Q | R }`), reaction-rule conservation (e.g.,
  MeTTa chemical abstract machine semantics), and token production
  ordering across parallel grammar categories.
- N01 flags reachable deadlock markings; N02 flags unbounded places
  (ω-marks in the Karp-Miller tree, indicating resource leaks).
- `PetriDeadlockCheck` in cost-benefit conditionally enables analysis —
  only grammars with concurrency constructs justify the EXPSPACE cost.
- `analyze_from_bundle()` constructs a Petri net from grammar concurrency
  constructs and runs Karp-Miller analysis, producing results wired
  into `LintContext`.

**Lints:** N01 petri-deadlock, N02 petri-unbounded.

### 8.10 Nominal Automata (Name-Binding)

**Source:** `nominal.rs` (feature: `nominal`)

**Theory:** Orbit-finite state spaces for name-passing calculi (Kaminski &
Francez 1994).  States are equivalent under name permutation, enabling
compact representation of infinite-alphabet behavior.

**Key operations:**
- `analyze_scope()` — verify atom is in scope
- `check_freshness()` — verify freshness constraints on bound names
- `compute_name_usage()` — compute name usage statistics across binders

**Pipeline integration:** Maps `Binder` and `BinderCollection` syntax items
to atom generation with equivariant transitions.

**Applications:**
- `analyze_scope()` verifies atom references within enclosing binders.
  `check_freshness()` verifies new names are distinct from all in-scope
  names.  `compute_name_usage()` tracks per-name usage counts (dead
  names, hot names).  `narrow_scope()` reduces binding live ranges when
  only a sub-branch references the name (e.g., Rholang `new x in
  { P | x!(Q) }` → `P | new x in { x!(Q) }`).  Orbit-finite
  representation groups states by name permutation equivalence for
  scalable infinite-alphabet analysis.
- Lexical scope enforcement (e.g., Rholang `new x in {P}` binder
  scoping), hygienic substitution (e.g., MeTTa `$y` capture avoidance),
  and alpha-equivalence detection (structurally identical definitions
  modulo renaming, enabling deduplication).
- N03 flags scope violations; N04 flags alpha-equivalent definitions;
  N05 flags freshness conflicts.
- `construct_nominal()` maps `Binder` and `BinderCollection` syntax
  items to orbit-finite automata with equivariant transitions.

**Lints:** N03 scope-violation, N04 alpha-equivalent, N05 fresh-conflict.

### 8.11 Cost Register Automata (CRA)

**Source:** `cra.rs` (feature: `cra`)

**Theory:** CRAs compute quantitative properties of input streams using
semiring-valued registers (Alur et al. 2013).

**Key type:**

```rust
struct CostRegisterAutomaton<W: Semiring> {
    num_states: usize,
    num_registers: usize,
    transitions: Vec<CraTransition>,
    initial_values: Vec<W>,      // register initialization
    output_registers: Vec<usize>, // which registers produce output
}

enum RegisterExpr {
    Reg(usize),           // read register
    InputCost,            // current input weight
    Zero, One,            // semiring constants
    Plus(Box, Box),       // ⊕
    Times(Box, Box),      // ⊗
}
```

**Operations:** `evaluate_stream()` processes (symbol, cost) pairs,
updating registers per transition.  `cra_check_equivalence_bounded()`
verifies behavioral equivalence over bounded input sequences.

**Applications:**
- `evaluate_stream()` processes (symbol, cost) pairs, updating registers
  per transition via `RegisterExpr` algebra (`Reg`, `InputCost`, `Zero`,
  `One`, `Plus`, `Times`) over any `Semiring`.
  `cra_check_equivalence_bounded()` verifies behavioral equivalence over
  bounded input sequences — validates that optimization transformations
  preserve quantitative semantics.
- Parse complexity metering (nesting depth, ambiguity count, recovery
  penalty as output registers), communication cost tracking (e.g.,
  Rholang per-channel send/receive cost), and rewrite step counting.
  Semiring-parameterized: `TropicalWeight` for min-cost,
  `CountingWeight` for path enumeration, `LogWeight` for
  probability-weighted costs.
- `analyze_from_bundle()` produces per-state register weights from the
  grammar's token stream, wired through `MathAnalysisResults`.

### 8.12 Morphism Analysis

**Source:** `morphism.rs` (feature: `morphisms`)

**Theory:** Theory morphisms are structure-preserving maps between algebraic
theories (sorts → sorts, operations → operations) that preserve axioms.

**Key operations:**
- `construct_morphism()` — validate structural preservation
- `verify_preservation()` — check all source axioms become target theorems
- `detect_gaps()` — identify unmapped sorts/operations
- `check_from_bundle()` — bridge morphism analysis to the pipeline

**Pipeline integration:** Maps grammar theories to shared theories for
modular proofs.  Results feed M01-M02 lints.

**Applications:**
- `construct_morphism()` validates structural preservation (sorts→sorts,
  operations→operations).  `verify_preservation()` checks source axioms
  become target theorems (e.g., β-reduction ↦ Comm rule, η-reduction ↦
  structural congruence).  `detect_gaps()` identifies unmapped sorts and
  operations, providing a checklist of missing translation cases.
- Translation verification (e.g., λ-calculus to process calculus
  formalization), verified desugaring (e.g., `let x = e in body` →
  `(λx.body) e` as semantics-preserving morphism), and modular grammar
  composition (shared subtheory maps into multiple grammars with
  cumulative proof transfer).
- M01 flags incomplete sort mappings (partial morphism); M02 flags
  axiom preservation failures (soundness violation in grammar
  transformation).
- `check_from_bundle()` extracts sort/op mappings from grammar syntax
  into `TheoryMorphism`.  Results feed M01-M02 lints.

### 8.13 Provenance Tracking

**Source:** `provenance.rs` (feature: `provenance`)

**Theory:** How-provenance semiring N[X] (Green et al. 2007) tracks *how*
each result is derived via polynomial bookkeeping.

```rust
struct ProvenanceWeight {
    // BTreeMap<Monomial, u64> — polynomial over base-fact variables
    // Monomial = BTreeMap<ProvenanceVar, u32> (variable → exponent)
}
```

**Projections:**
- `to_boolean()` — any derivation? (which-provenance)
- `to_counting()` — total derivation count
- `evaluate<W>(valuation)` — homomorphism to any semiring W

**Pipeline integration:** Labels become provenance variables; results feed
proof output for derivation certificates.

**Applications:**
- `ProvenanceWeight` (`BTreeMap<Monomial, u64>`) tracks derivation
  polynomials over base-fact variables.  Monomial multiplication records
  conjunctive steps (A ∧ B); polynomial addition records alternative
  paths (A ∨ B).
- `to_boolean()` answers existence (which-provenance); `to_counting()`
  gives derivation counts (how-many-provenance); `evaluate::<W>()`
  provides homomorphic projection — `TropicalWeight` for min-cost,
  `CountingWeight` for enumeration, `BooleanWeight` for existence.
- Derivation explanation (e.g., MeTTa unexpected rewrite tracing via
  `all_variables()`), process lineage (e.g., Rholang reduction sequences
  as polynomial terms), and grammar rule cost attribution via
  `TropicalWeight` projection.
- Grammar rule labels become `ProvenanceVar` in `N[X]`.
  `track_from_bundle()` produces provenance weights consumed by
  `proof_output` to populate proof step `base_facts`, linking each
  certificate step to the grammar rules that justify it.

### 8.14 Proof Output

**Source:** `proof_output.rs` (feature: `proofs`)

The proof output module generates layered certificates:

1. **Verdict** (always): `Verified`, `Violated`, or `Unknown`
2. **Human-readable** (feature `proofs`): numbered proof steps with
   justifications and provenance tracking
3. **Rocq certificate** (feature `proofs`): machine-checkable `Theorem` +
   `Proof` skeleton (with `Admitted` for verification gaps)

**Applications:**
- Three-tier output: Verdict (always: `Verified`/`Violated`/`Unknown`),
  human-readable (feature `proofs`: numbered steps with justifications
  and provenance via `to_human_readable()`), and Rocq certificate
  (feature `proofs`: machine-checkable `Theorem`+`Proof` skeleton via
  `generate_rocq_certificate()`).  `Admitted` markers flag proof
  obligations not automatically dischargeable.
- Each `ProofStep` references `ProvenanceVar` base facts, providing
  end-to-end traceability from grammar rules through analysis to
  certificate.
- Compile-time correctness certificates (confluence + termination +
  safety → confidence certificate), human-readable audit reports, and
  deployment evidence chains (e.g., Rholang smart contract verification).
- `generate_certificates()` consumes `ConfluenceAnalysis`,
  `TerminationResult`, and `SafetyResult` from earlier pipeline phases,
  bundling all verdicts into `ProofOutput`.

---

## 9. Integration: How It All Fits Together

### 9.1 Full Pipeline Phase Diagram

```
┌────────────────────────────────────────────────────────────────┐
│                     PraTTaIL Pipeline                          │
├────────────────────────────────────────────────────────────────┤
│                                                                │
│  Phase 0: Extract                                              │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │ LanguageSpec → LexerBundle + ParserBundle (Send+Sync)    │  │
│  │ Terminal collection, mixfix extraction, RD conversion    │  │
│  └───────────────────────┬──────────────────────────────────┘  │
│                          │                                     │
│  Phase 1: Lexer Codegen  │  Phase 2: Parser Analysis           │
│  ┌───────────────┐       │  ┌───────────────────────────────┐  │
│  │ NFA → DFA →   │       │  │ 2a. Binding Power Analysis    │  │
│  │ minimize →    │       │  │ 2b. FIRST/FOLLOW sets (DB01)  │  │
│  │ codegen       │       │  │ 2c. Cross-category overlaps   │  │
│  │               │       │  │ 2d. WFST construction         │  │
│  │ Output:       │       │  │ 2e. Dead-rule detection       │  │
│  │ lexer_code    │       │  │ 2f. Decision tree (PathMap)   │  │
│  │ variant_map   │       │  │ 2g. Cost-benefit evaluation   │  │
│  │ ambiguity_info│       │  └───────────────────────────────┘  │
│  └───────────────┘       │                                     │
│                          │  Phase 3: Math Analyses (parallel)  │
│                          │  ┌───────────────────────────────┐  │
│                          │  │ std::thread::scope {          │  │
│                          │  │   TRS: confluence, termination│  │
│                          │  │   VPA, WTA                    │  │
│                          │  │   Safety, CEGAR, Algebraic    │  │
│                          │  │   Petri, Nominal              │  │
│                          │  │   LTL, Buchi                  │  │
│                          │  │   Provenance, CRA, Morphism   │  │
│                          │  │   KAT, Proof Output           │  │
│                          │  │   Advanced Automata (M1-M11)  │  │
│                          │  │   Predicate Dispatch          │  │
│                          │  │ }                             │  │
│                          │  └───────────────────────────────┘  │
│                          │                                     │
│  Phase 4: Codegen        │                                     │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │ 4a. Lint emission (60+ diagnostics)                      │  │
│  │ 4b. Trampoline codegen (continuation stack)              │  │
│  │ 4c. Recovery codegen (WFST-weighted repair)              │  │
│  │ 4d. RD handler generation                                │  │
│  │ 4e. Dispatch codegen (decision tree → match arms)        │  │
│  └──────────────────────────────────────────────────────────┘  │
│                                                                │
│  Phase 5: Finalize                                             │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │ Concatenate lexer_code + parser_code → String            │  │
│  │ str::parse::<TokenStream>() → TokenStream                │  │
│  │ PipelineAnalysis → macros for Ascent codegen             │  │
│  └──────────────────────────────────────────────────────────┘  │
│                                                                │
└────────────────────────────────────────────────────────────────┘
```

### 9.2 Feedback Loops

```
┌───────────────────┐         ┌─────────────────────────┐
│ PipelineAnalysis  ├────────→│ Ascent Codegen (macros) │
│  dead_rule_labels │  DCE    │  Skip dead rules        │
│  constructor_     │  order  │  Reorder join clauses   │
│    weights        │         │  Template instantiation │
│  isomorphic_      │         │  Demand-driven DCE      │
│    groups         │         └─────────────────────────┘
└───────────────────┘

┌───────────────────┐         ┌─────────────────────────┐
│ WFST weights      ├────────→│ Decision tree ordering  │
│  per-action       │  rank   │  Commit vs Ambiguous    │
│  beam width       │         │  DisjointSuffix mode    │
└───────────────────┘         └─────────────────────────┘

┌───────────────────┐         ┌─────────────────────────┐
│ Recovery weights  ├────────→│ Context scaling         │
│  follow_contexts  │  filter │  Bracket penalties      │
│  prediction_      │         │  Depth adaptation       │
│    discounts      │         └─────────────────────────┘
└───────────────────┘

┌───────────────────┐         ┌─────────────────────────┐
│ Advanced Automata ├────────→│ Lint enrichment         │
│  symbolic_result  │  enrich │  SYM01-04, O01-02,      │
│  buchi_result     │         │  PT01-03, RA01-03,      │
│  vpa_result       │         │  PR01-04, etc.          │
│  ...              │         └─────────────────────────┘
└───────────────────┘
```

### 9.3 PipelineAnalysis Export

The `PipelineAnalysis` struct is the primary output from PraTTaIL to the
macro layer.  It carries analysis results that inform Ascent Datalog codegen:

```rust
pub struct PipelineAnalysis {
    // Always available
    pub dead_rule_labels: HashSet<String>,
    pub unreachable_categories: HashSet<String>,
    pub constructor_weights: HashMap<String, f64>,
    pub category_weights: HashMap<String, f64>,
    pub isomorphic_groups: Vec<Vec<String>>,
    pub isomorphic_action_maps: Vec<HashMap<u32, Vec<(String, String)>>>,
    pub decision_trees: HashMap<String, CategoryDecisionTree>,

    // Feature-gated (selected examples)
    #[cfg(feature = "register-automata")]
    pub dead_binder_categories: HashSet<String>,
    #[cfg(feature = "vpa")]
    pub bracket_deterministic: bool,
    #[cfg(feature = "vpa")]
    pub vpa_max_nesting_bound: Option<usize>,
    #[cfg(feature = "multi-tape")]
    pub independent_categories: HashSet<String>,
    #[cfg(feature = "symbolic-automata")]
    pub guard_disambiguated_tokens: HashSet<String>,
    #[cfg(feature = "probabilistic")]
    pub per_category_entropy: HashMap<String, f64>,
    #[cfg(feature = "omega")]
    pub recursive_scc_categories: HashSet<String>,
}
```

**How macros use PipelineAnalysis:**

| Field                    | Macro Action                                                |
|--------------------------|-------------------------------------------------------------|
| `dead_rule_labels`       | DCE: skip Ascent rule generation for dead rules             |
| `constructor_weights`    | Order join clauses by weight (hot constructors first)       |
| `category_weights`       | Order category-level evaluation                             |
| `isomorphic_groups`      | Template instantiation (share codegen for isomorphic rules) |
| `decision_trees`         | Downstream composition analysis                             |
| `dead_binder_categories` | Skip binder infrastructure for unused binder categories     |
| `per_category_entropy`   | Adaptive beam width in generated parser                     |

### 9.4 Composition

The `compose_languages()` function merges two `LanguageSpec` values:

1. **Categories**: Union by name; native type mismatches are errors
2. **Rules**: Concatenated; labels must be globally unique
3. **Validation**: Category references, associativity conflicts, BP conflicts
4. **Reclassification**: All derived flags re-derived via `classify_rule()`
5. **FIRST/FOLLOW**: Automatically recomputed by the pipeline

The DSL supports four composition clauses:

| Clause               | Scope                                                  | Strategy    |
|----------------------|--------------------------------------------------------|-------------|
| `extends: [Base]`    | Full (types + terms + equations + rewrites + logic)    | Inheritance |
| `includes: [Lib]`    | Grammar-only (types + terms)                           | Override    |
| `mixins: [Fragment]` | Grammar-only (types + terms from `language_fragment!`) | Override    |
| `compose_languages!` | Programmatic merge of two `LanguageSpec` values        | Union       |

**Composition validation:**

```rust
pub enum CompositionError {
    CategoryNativeTypeMismatch {
        category: String,
        native_type_a: Option<String>,
        native_type_b: Option<String>,
    },
    DuplicateRuleLabel {
        label: String,
        category_a: String,
        category_b: String,
    },
    InvalidCategoryReference {
        rule_label: String,
        referenced_category: String,
    },
    AssociativityConflict {
        terminal: String, category: String,
        assoc_a: Associativity, assoc_b: Associativity,
    },
    BindingPowerConflict {
        terminal: String, category: String,
        bp_a: u8, bp_b: u8,
    },
}
```

**Merge strategy:**
1. Categories from spec_a come first (ordering preserved)
2. Categories unique to spec_b appended after
3. First grammar's primary category wins
4. All rules reclassified via `classify_rule()` after merge
5. FIRST/FOLLOW sets automatically recomputed by pipeline

**Composition lints (X01-X05)** report issues detected during merge, such
as category mismatches, rule label collisions, and reference validation
failures.  These are collected as `pre_collected_diagnostics` in the
`LintContext` and emitted alongside pipeline-generated diagnostics.

---

## Appendices

### A. Complete Semiring Quick-Reference

| #  | Name                   | (⊕, ⊗)         | Idempotent | Star  | Feature           |
|----|------------------------|----------------|:----------:|:-----:|-------------------|
| 1  | TropicalWeight         | (min, +)       |     ✓      |   ✓   | core              |
| 2  | CountingWeight         | (+, ×)         |     ✗      |   ✓   | core              |
| 3  | BooleanWeight          | (∨, ∧)         |     ✓      |   ✓   | core              |
| 4  | EditWeight             | (min, +)       |     ✓      |   ✓   | core              |
| 5  | ProductWeight\<A,B\>   | (comp, comp)   |    A∧B     |  A∧B  | core              |
| 6  | ContextWeight          | (∪, ∩)         |     ✓      |   ✓   | core              |
| 7  | ComplexityWeight       | (min, max)     |     ✓      |   ✓   | core              |
| 8  | ViterbiWeight          | (max, ×)       |     ✓      |   ✓   | core              |
| 9  | ArcticWeight           | (max, +)       |     ✓      |   ✓   | core              |
| 10 | FuzzyWeight            | (max, min)     |     ✓      |   ✓   | core              |
| 11 | TruncationWeight\<K\>  | (max, sat+)    |     ✓      |   ✗   | core              |
| 12 | NbestWeight\<N\>       | (merge, cross) |     ✗      |   ✗   | core              |
| 13 | TensorWeight\<W1,W2\>  | (cat, bilin)   |   W1∧W2    | W1∧W2 | core              |
| 14 | LogWeight              | (lse, +)       |     ✗      |   ✓   | wfst-log          |
| 15 | EntropyWeight          | (lse+mix, +)   |     ✗      |   ✓   | wfst-log          |
| 16 | AmplitudeWeight        | (ℂ+, ℂ×)       |     ✗      |   ✗   | quantum           |
| 17 | MultisetWeight         | (pmax, padd)   |     —      |   —   | multiset-automata |
| 18 | TropicalMultisetWeight | (pmin, padd)   |     —      |   —   | multiset-automata |
| 19 | RelationalWeight\<G\>  | (∪, ;)         |     —      |   —   | wpds-relational   |
| 20 | ProvenanceWeight       | (poly+, poly×) |     —      |   —   | provenance        |

### B. Feature Flag Reference

| Feature                | Dependencies                                                                                                                | Module(s)               |
|------------------------|-----------------------------------------------------------------------------------------------------------------------------|-------------------------|
| `wfst-log`             | dep:serde, dep:postcard                                                                                                     | `log_push.rs`, `training.rs`                |
| `quantum`              | dep:num-complex                                                                                                             | `semiring.rs` (AmplitudeWeight)             |
| `simd-whitespace`      | (none)                                                                                                                      | AL03 SIMD whitespace                        |
| `grammar-gen`          | dep:proptest                                                                                                                | `grammar_gen.rs`                            |
| `wpds-relational`      | (none)                                                                                                                      | `relational.rs`                             |
| `wpds-extended`        | (none)                                                                                                                      | `ewpds.rs`                                  |
| `wpds-ara`             | dep:nalgebra, wpds-relational                                                                                               | `ara.rs`                                    |
| `provenance`           | (none)                                                                                                                      | `provenance.rs`                             |
| `proofs`               | provenance                                                                                                                  | `proof_output.rs`                           |
| `trs-analysis`         | (none)                                                                                                                      | `confluence.rs`, `termination.rs`           |
| `vpa`                  | (none)                                                                                                                      | `vpa.rs`                                    |
| `tree-automata`        | (none)                                                                                                                      | `tree_automaton.rs`                         |
| `omega`                | (none)                                                                                                                      | `buchi.rs`                                  |
| `ltl`                  | omega                                                                                                                       | `ltl.rs`                                    |
| `alternating`          | (none)                                                                                                                      | `alternating.rs`                            |
| `nominal`              | (none)                                                                                                                      | `nominal.rs`                                |
| `petri`                | (none)                                                                                                                      | `petri.rs`                                  |
| `cra`                  | (none)                                                                                                                      | `cra.rs`                                    |
| `kat`                  | (none)                                                                                                                      | `kat.rs`                                    |
| `morphisms`            | (none)                                                                                                                      | `morphism.rs`                               |
| `symbolic-automata`    | kat                                                                                                                         | `symbolic.rs`                               |
| `weighted-mso`         | symbolic-automata                                                                                                           | `weighted_mso.rs`                           |
| `parity-tree-automata` | alternating, tree-automata                                                                                                  | `parity_tree.rs`                            |
| `register-automata`    | nominal                                                                                                                     | `register_automata.rs`                      |
| `probabilistic`        | wfst-log                                                                                                                    | `probabilistic.rs`                          |
| `multi-tape`           | wfst-log                                                                                                                    | `multi_tape.rs`                             |
| `multiset-automata`    | (none)                                                                                                                      | `multiset_automata.rs`                      |
| `two-way-transducer`   | wfst-log                                                                                                                    | `two_way_transducer.rs`                     |
| `predicate-dispatch`   | symbolic-automata, weighted-mso                                                                                             | `predicate_dispatch.rs`                     |
| `analysis`             | tree-automata, vpa, trs-analysis                                                                                            | (convenience)           |
| `verification`         | omega, ltl, kat, wpds-relational                                                                                            | (convenience)           |
| `process-algebra`      | nominal, petri, omega, alternating, symbolic-automata, two-way-transducer                                                   | (convenience)           |
| `predicated-types`     | symbolic-automata, weighted-mso, parity-tree-automata, register-automata, multi-tape, multiset-automata, two-way-transducer | (convenience)           |
| `full-analysis`        | (all of the above)                                                                                                          | (convenience)           |

### C. Lint Code Directory

**Grammar (G):**
G01 left-recursion, G02 unused-category, G03 ambiguous-prefix,
G04 duplicate-rule-label, G05 empty-category, G06 shadowed-operator,
G07 identical-rules, G08 missing-cast-to-root, G09 unbalanced-delimiters,
G24 alpha-equivalent-rules, G32 prefix-isomorphism.

**WFST (W):**
W01 dead-rule, W02 nfa-ambiguous-prefix, W03 high-ambiguity-token,
W04 weight-gap-anomaly, W06 weight-inversion,
W10 spillover-eliminable-by-lookahead, W11 context-narrowing-deterministic,
W12 training-would-improve, W13 wpds-unreachable,
W14 wpds-confirmed-ambiguity, W16 wpds-weight-inversion.

**Recovery (R):**
R01 empty-sync-set, R02 sparse-recovery, R05 missing-bracket-sync,
R06 inverted-recovery-costs, R07 transposition-candidate.

**Cross-Category (C):**
C01 cast-cycle, C02 transitive-cast-redundancy, C04 wide-cross-overlap.

**Composition (X):**
X01-X05.

**Performance (P):**
P02 high-nfa-spillover, P03 deep-cast-nesting, P04 many-alternatives,
P05 wpds-pipeline-cost, P06 analysis-pipeline-cost.

**Diagnostics (D):**
D10 lookahead-waste, D13 ascent-trie-correlation, D14 wpds-complexity-report.

**Infrastructure (I):**
I01, I04, I08, I10, I17, I18.

**TRS (T):**
T01 non-joinable-pair, T02 non-terminating, T03 critical-pair-found,
T04 termination-unknown.

**VPA/WTA (V):**
V01 vpa-determinizable, V02 alphabet-mismatch, V03 wta-unrecognized,
V04 wta-hot-path, V05 weighted-determinization, V06 stack-alphabet.

**Safety/CEGAR (S):**
S01 safety-violation, S02 safety-verified, S03 cegar-iteration,
S04 cegar-converged, S05 cegar-timeout, S06 invariant-suggestion.

**Concurrency (N):**
N01 petri-deadlock, N02 petri-unbounded, N03 nominal-scope-violation,
N04 nominal-alpha-equivalent, N05 nominal-fresh-conflict,
N06 polynomial-iso-anomaly, N07 branching-imbalance.

**LTL (L):**
L01 ltl-violated, L02 ltl-satisfied.

**Provenance/CRA (E):**
E01 provenance-gap, E02 cra-anomaly.

**Morphisms (M):**
M01 morphism-gap, M02 morphism-complete.

**KAT (K):**
K01 kat-inequivalence, K02 kat-equivalent.

**Ascent Codegen (A):**
A01-A10 (codegen optimization diagnostics).

**Lexer Optimization (LEX):**
LEX02-LEX05.

**Parser Optimization (PAR):**
PAR01-PAR05.

**Dispatch Optimization (DIS):**
DIS01-DIS05.

**Advanced Automata:**
SYM01-04 (symbolic), O01-02 (omega/Buchi), PT01-03 (parity tree),
RA01-03 (register), PR01-04 (probabilistic), MT01-02 (multi-tape),
MS01-02 (multiset), MSO01-03 (weighted MSO), TW01-03 (two-way),
PD01-04 (predicate dispatch).

### C.1 Lint Severity Levels

| Severity | ANSI Color  | Meaning               | Action                               |
|----------|-------------|-----------------------|--------------------------------------|
| Error    | Bold red    | Correctness bug       | Must fix before compilation succeeds |
| Warning  | Bold yellow | Possible issue        | Review recommended                   |
| Note     | Bold cyan   | Informational         | No action required                   |
| Info     | Bold cyan   | Infrastructure status | Pipeline progress                    |

### D. Glossary

| Term                      | Definition                                                            |
|---------------------------|-----------------------------------------------------------------------|
| **AST**                   | Abstract syntax tree                                                  |
| **AWA**                   | Weighted alternating automaton                                        |
| **BFS**                   | Breadth-first search                                                  |
| **Binding power (BP)**    | Numeric precedence value controlling operator parsing order           |
| **Category**              | A syntactic sort in the grammar (e.g., `Int`, `Bool`)                 |
| **CEGAR**                 | Counterexample-guided abstraction refinement                          |
| **Codepoint**             | Unicode scalar value (U+0000 to U+10FFFF, excluding surrogates)      |
| **Congruence rule**       | Rewrite rule enabling reduction under a constructor context           |
| **CRA**                   | Cost register automaton                                               |
| **CSE**                   | Common subexpression elimination                                      |
| **CTMC**                  | Continuous-time Markov chain                                          |
| **DAG**                   | Directed acyclic graph                                                |
| **DCE**                   | Dead-code elimination                                                 |
| **Dead rule**             | A grammar rule that can never be reached during parsing               |
| **Decision tree**         | PathMap trie for token-based parse dispatch                           |
| **DFA**                   | Deterministic finite automaton                                        |
| **DFS**                   | Depth-first search                                                    |
| **DSL**                   | Domain-specific language                                              |
| **EBNF**                  | Extended Backus-Naur Form                                             |
| **Edit distance**         | Minimum number of token-level edits to repair a parse                 |
| **EM**                    | Expectation-maximization (Baum-Welch parameter estimation)            |
| **Equivalence class**     | Set of input bytes with identical NFA transitions                     |
| **EWPDS**                 | Extended weighted pushdown system (WPDS with merge functions)         |
| **FIRST set**             | Set of tokens that can begin a category derivation                    |
| **FOLLOW set**            | Set of tokens that can appear after a category                        |
| **FST**                   | Finite-state transducer                                               |
| **HeapSemiring**          | Semiring trait without `Copy` bound (HashMap-backed weights)          |
| **Hopcroft minimization** | Algorithm to minimize DFA state count                                 |
| **KAT**                   | Kleene Algebra with Tests                                             |
| **LED**                   | Left denotation: Pratt parser handler for infix/postfix operators     |
| **LTL**                   | Linear temporal logic                                                 |
| **Minterm**               | Atom of the Boolean algebra of guard predicates                       |
| **MPH**                   | Minimal perfect hash (O(1) keyword lookup)                            |
| **MSO**                   | Monadic Second-Order logic                                            |
| **NBA**                   | Nondeterministic Büchi automaton                                      |
| **NFA**                   | Nondeterministic finite automaton                                     |
| **NUD**                   | Null denotation: Pratt parser handler for prefix/atom                 |
| **P-automaton**           | Automaton accepting stack configurations (WPDS result)                |
| **PATA**                  | Parity alternating tree automaton                                     |
| **PathMap**               | Trie data structure for byte-sequence dispatch                        |
| **PDA**                   | Pushdown automaton                                                    |
| **Pipeline analysis**     | `PipelineAnalysis` struct exported to macros for codegen optimization |
| **Poststar**              | Forward reachability computation for WPDS                             |
| **Prestar**               | Backward reachability computation for WPDS                            |
| **RD**                    | Recursive descent                                                     |
| **REPL**                  | Read-eval-print loop                                                  |
| **SCC**                   | Strongly connected component (Tarjan's algorithm)                     |
| **Semiring**              | Algebraic structure (K, ⊕, ⊗, 0̄, 1̄)                                   |
| **SFA**                   | Symbolic finite automaton                                             |
| **SGD**                   | Stochastic gradient descent                                           |
| **StarSemiring**          | Semiring with Kleene closure operation a*                             |
| **Thompson construction** | NFA construction from regular expressions                             |
| **Trampoline**            | Explicit continuation stack replacing OS call stack                   |
| **TRS**                   | Term rewriting system                                                 |
| **Unicode property**      | Named character class from the Unicode standard (e.g., `XID_Start`, `Letter`, `Greek`) |
| **UTF-8 byte chain**      | Sequence of byte-range NFA transitions encoding a multi-byte Unicode codepoint |
| **Utf8Sequences**         | `regex-syntax` API that decomposes codepoint ranges into minimal byte-range chains |
| **VPA**                   | Visibly pushdown automaton                                            |
| **WFSA**                  | Weighted finite-state automaton                                       |
| **WFST**                  | Weighted finite-state transducer                                      |
| **WPDS**                  | Weighted pushdown system                                              |
| **WTA**                   | Weighted tree automaton                                               |

### E. References

- Aho, A. V., Lam, M. S., Sethi, R., & Ullman, J. D. (2006). *Compilers: Principles, Techniques, and Tools* (2nd ed.). Addison-Wesley.
- Alur, R., D'Antoni, L., Deshmukh, J., Raghothaman, M., & Yuan, Y. (2013). Regular functions and cost register automata. *LICS 2013*, 13-22.
- Alur, R., & Madhusudan, P. (2004). Visibly pushdown languages. *STOC 2004*, 202-211.
- Arts, T., & Giesl, J. (2000). Termination of term rewriting using dependency pairs. *Theoretical Computer Science*, 236(1-2), 133-178.
- Buchi, J. R. (1962). On a decision method in restricted second order arithmetic. *Logic, Methodology and Philosophy of Science*, 1-11.
- Chandra, A. K., Kozen, D. C., & Stockmeyer, L. J. (1981). Alternation. *Journal of the ACM*, 28(1), 114-133.
- D'Antoni, L., & Veanes, M. (2017). The power of symbolic automata and transducers. *CAV 2017*, LNCS 10426, 47-67.
- Droste, M., & Gastin, P. (2007). Weighted automata and weighted logics. *Theoretical Computer Science*, 380(1-2), 69-86.
- Droste, M., Kuich, W., & Vogler, H. (2009). *Handbook of Weighted Automata*. Springer.
- Eilenberg, S. (1976). *Automata, Languages, and Machines, Vol. B*. Academic Press.
- Emerson, E. A., & Jutla, C. S. (1991). Tree automata, mu-calculus and determinacy. *FOCS 1991*, 368-377.
- Esparza, J., Kiefer, S., & Luttenberger, M. (2010). Newton's method for ω-continuous semirings. *ICALP 2010*, LNCS 6199, 14-26.
- Feng, Q., & Maletti, A. (2022). Two-way weighted automata. *DLT 2022*.
- Green, T. J., Karvounarakis, G., & Tannen, V. (2007). Provenance semirings. *PODS 2007*, 31-40.
- Hopcroft, J. E. (1971). An n log n algorithm for minimizing states in a finite automaton. *Theory of Machines and Computations*, 189-196.
- Karp, R. M., & Miller, R. E. (1969). Parallel program schemata. *Journal of Computer and System Sciences*, 3(2), 147-195.
- Kaminski, M., & Francez, N. (1994). Finite-memory automata. *Theoretical Computer Science*, 134(2), 329-363.
- Kempe, A. (2004). Weighted finite-state transducer compilation of multi-tape automata. *LNCS 3317*, 189-198.
- Kincaid, Z., Cyphert, J., Breck, J., & Reps, T. (2019). Non-linear reasoning for invariant synthesis. *POPL 2019*.
- Knuth, D. E., & Bendix, P. B. (1970). Simple word problems in universal algebras. *Computational Problems in Abstract Algebra*, 263-297.
- Kozen, D. (1997). Kleene algebra with tests. *TOPLAS*, 19(3), 427-443.
- Mohri, M. (2009). Weighted automata algorithms. In *Handbook of Weighted Automata* (pp. 213-254). Springer.
- Muller, T., Weiss, B., & Lochau, M. (2024). Featured multiset automata for software product-line analysis. *FASE 2024*.
- Pratt, V. R. (1973). Top down operator precedence. *POPL 1973*, 41-51.
- Rabiner, L. R. (1989). A tutorial on hidden Markov models. *Proceedings of the IEEE*, 77(2), 257-286.
- Rabin, M. O., & Scott, D. (1959). Finite automata and their decision problems. *IBM Journal of Research and Development*, 3(2), 114-125.
- Reps, T., Lal, A., & Kidd, N. (2007). Program analysis using weighted pushdown systems. *FSTTCS 2007*, LNCS 4855, 23-51.
- Thompson, K. (1968). Programming techniques: Regular expression search algorithm. *Communications of the ACM*, 11(6), 419-422.
- Unicode Consortium. (2023). *The Unicode Standard, Version 15.1.0*. Unicode, Inc. [unicode.org/versions/Unicode15.1.0](https://unicode.org/versions/Unicode15.1.0/)
- Viterbi, A. J. (1967). Error bounds for convolutional codes. *IEEE Transactions on Information Theory*, 13(2), 260-269.
- Wagner, R. A., & Fischer, M. J. (1974). The string-to-string correction problem. *Journal of the ACM*, 21(1), 168-173.
