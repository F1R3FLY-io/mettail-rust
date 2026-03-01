# Token Lattice Architecture and Pipeline Integration

**Date:** 2026-03-01

This document maps every integration point between the token lattice
subsystem and the rest of PraTTaIL: where lattices are constructed,
queried, and resolved across the compile-time pipeline and at runtime.
For formal theory, see
[theory/wfst/token-lattices.md](../../theory/wfst/token-lattices.md).
For design rationale, see
[design/wfst/token-lattices.md](../../design/wfst/token-lattices.md).

---

## Table of Contents

1. [Motivation](#1-motivation)
2. [Module Dependency Graph](#2-module-dependency-graph)
3. [Compile-Time vs Runtime Usage](#3-compile-time-vs-runtime-usage)
   - 3.1 [Compile-Time](#31-compile-time)
   - 3.2 [Runtime](#32-runtime)
4. [Integration with Error Recovery](#4-integration-with-error-recovery)
   - 4.1 [Recovery WFST as Implicit Lattice](#41-recovery-wfst-as-implicit-lattice)
   - 4.2 [viterbi_multi_step()](#42-viterbi_multi_step)
   - 4.3 [lattice_recovery()](#43-lattice_recovery)
   - 4.4 [EditWeight Integration](#44-editweight-integration)
5. [Integration with Composed Dispatch](#5-integration-with-composed-dispatch)
   - 5.1 [Weight Maps, Not Lattices](#51-weight-maps-not-lattices)
   - 5.2 [Conceptual Lattice](#52-conceptual-lattice)
   - 5.3 [Why TokenLattice Is Not Used](#53-why-tokenlattice-is-not-used)
6. [Integration with Grammar Composition](#6-integration-with-grammar-composition)
   - 6.1 [No Direct Lattice Use](#61-no-direct-lattice-use)
   - 6.2 [Ambiguities from Composition](#62-ambiguities-from-composition)
7. [Integration with NFA Disambiguation](#7-integration-with-nfa-disambiguation)
   - 7.1 [Thread-Local Weight Annotation](#71-thread-local-weight-annotation)
   - 7.2 [Spillover as Implicit Lattice](#72-spillover-as-implicit-lattice)
8. [Integration with Weight Training (wfst-log)](#8-integration-with-weight-training-wfst-log)
   - 8.1 [Forward-Backward and Raw Adjacency Lists](#81-forward-backward-and-raw-adjacency-lists)
   - 8.2 [Parse Lattice Construction](#82-parse-lattice-construction)
9. [Generated Code Anatomy](#9-generated-code-anatomy)
   - 9.1 [Lexer Entry Point](#91-lexer-entry-point)
   - 9.2 [Currently Always Linear](#92-currently-always-linear)
   - 9.3 [Future Context-Sensitive Lexing](#93-future-context-sensitive-lexing)
10. [Data Flow Summary](#10-data-flow-summary)
11. [Source Map](#11-source-map)
12. [Cross-References](#12-cross-references)

---

## 1. Motivation

The token lattice is not an isolated data structure — it is a nexus
connecting four subsystems: the lexer (which produces lattices), the
parser (which consumes them via Viterbi), error recovery (which builds
implicit repair lattices), and weight training (which computes posteriors
over them). This document maps every edge in that dependency graph.

---

## 2. Module Dependency Graph

```
  ┌─────────────────────────────────────────────────────────────────────┐
  │  Compile-time pipeline                                              │
  │                                                                     │
  │  ┌─────────────────┐                                                │
  │  │   pipeline.rs    │                                                │
  │  │ (state machine)  │                                                │
  │  └────────┬────────┘                                                │
  │           │ generate_parser_code()                                   │
  │           ▼                                                         │
  │  ┌─────────────────┐   FIRST/FOLLOW   ┌──────────────────┐         │
  │  │  prediction.rs   │ ───────────────►│     wfst.rs       │         │
  │  │ (sets, overlap)  │                 │ (PredictionWfst)  │         │
  │  └─────────────────┘                  └──────────────────┘         │
  │                                                                     │
  │  ┌─────────────────┐                  ┌──────────────────┐         │
  │  │  compose.rs      │                 │   dispatch.rs     │         │
  │  │ (grammar union)  │                 │ (codegen match)   │         │
  │  └─────────────────┘                  └──────────────────┘         │
  └─────────────────────────────────────────────────────────────────────┘

  ┌─────────────────────────────────────────────────────────────────────┐
  │  Runtime (generated + library code)                                 │
  │                                                                     │
  │                     ┌───────────────────┐                           │
  │                     │   semiring.rs      │                           │
  │                     │ TropicalWeight     │                           │
  │                     │ EditWeight         │                           │
  │                     │ CountingWeight     │                           │
  │                     │ BooleanWeight      │                           │
  │                     │ ProductWeight      │                           │
  │                     │ LogWeight†         │                           │
  │                     └────────┬──────────┘                           │
  │                              │                                      │
  │             ┌────────────────┼────────────────┐                     │
  │             ▼                ▼                ▼                     │
  │  ┌──────────────────┐ ┌──────────┐ ┌──────────────────────┐        │
  │  │    lattice.rs     │ │recovery.rs│ │forward_backward.rs† │        │
  │  │ TokenSource       │ │RecoveryWfst│ │ forward/backward   │        │
  │  │ TokenLattice      │ │RepairAction│ │ posteriors         │        │
  │  │ ViterbiPath       │ │viterbi_   │ └──────────────────────┘        │
  │  │ viterbi_best_path │ │multi_step │                                │
  │  │ viterbi_generic   │ │lattice_   │ ┌──────────────────────┐        │
  │  │ n_best_paths†     │ │recovery‡  │ │   training.rs†       │        │
  │  │ alternative_paths‡│ └───────────┘ │ SGD weight updates   │        │
  │  └──────────────────┘                └──────────────────────┘        │
  │                                                                     │
  │  † = wfst-log gated    ‡ = context-sensitive-lex gated              │
  └─────────────────────────────────────────────────────────────────────┘
```

Key observations:

- **lattice.rs** depends only on **semiring.rs** — it has no dependencies
  on prediction, dispatch, or pipeline modules.
- **recovery.rs** uses lattice *concepts* (Viterbi DP, repair edges) but
  implements its own repair lattice inline — it does NOT import
  `TokenLattice`.
- **forward_backward.rs** and **training.rs** use raw adjacency lists
  that are structurally similar to `TokenLattice` but are not the same
  type (they operate over `(state, state, weight)` triples).

---

## 3. Compile-Time vs Runtime Usage

### 3.1 Compile-Time

At compile time (inside the proc-macro), the pipeline **does not
construct `TokenLattice` objects**. Instead, it uses lattice *concepts*
implicitly:

| Pipeline stage               | Lattice concept                       | Implementation              |
|:-----------------------------|:--------------------------------------|:----------------------------|
| FIRST/FOLLOW computation     | None — set-based analysis             | `prediction.rs`             |
| WFST construction            | Weighted automaton (not lattice)      | `wfst.rs`                   |
| Dead-rule detection          | BooleanWeight reachability            | `pipeline.rs`               |
| Ambiguity warnings           | CountingWeight path counting          | `pipeline.rs`               |
| Codegen                      | Emits `TokenSource`, `lex_weighted()` | `automata/codegen.rs`       |

The pipeline emits code that *uses* `TokenSource` and `lex_weighted()`
at runtime, but the pipeline itself never instantiates lattice objects.

### 3.2 Runtime

At runtime, `TokenSource` is the primary abstraction:

1. **Generated lexer** (`lex_weighted_core()`) produces
   `Vec<(Token<'a>, Range, f64)>` triples.
2. `TokenSource::from_weighted()` converts to `TokenSource::Linear`
   (stripping weights; currently always linear).
3. `TokenSource::resolve()` extracts the flat token vector (identity on
   Linear, Viterbi on Lattice).
4. The **parser** (`parse_Cat()`) consumes `Vec<(Token<'a>, Range)>`.

The Lattice variant is activated only when:

- `context-sensitive-lex` is enabled AND
- The lexer detects actual lexical ambiguity (multiple tokens at one
  position)

For all current grammars, the Linear path is always taken.

---

## 4. Integration with Error Recovery

### 4.1 Recovery WFST as Implicit Lattice

Error recovery in `recovery.rs` constructs a **repair lattice** — a
weighted DAG where:

- Nodes = positions in the remaining token stream (0 to max_lookahead)
- Edges = repair actions (skip, delete, substitute, insert, sync)
- Weights = repair costs (`TropicalWeight`)
- Sink = virtual node representing a sync point

This is structurally identical to a `TokenLattice`, but it is implemented
inline using arrays (`dist[]`, `pred[]`) rather than a `TokenLattice`
object. The reason is efficiency: the repair lattice is small (≤32 nodes),
fixed-size, and immediately consumed — allocating a `Vec<Vec<LatticeEdge>>`
would add unnecessary indirection.

```
  ┌──────────────────────────────────────────────────────────────────┐
  │  Error recovery data flow                                        │
  │                                                                  │
  │  Parse error at position P                                       │
  │         │                                                        │
  │         ▼                                                        │
  │  token_ids[P..P+32]  ──► viterbi_multi_step()                    │
  │                          │                                       │
  │                          ├── Build implicit repair lattice       │
  │                          │   ┌───┐ skip ┌───┐ skip ┌───┐        │
  │                          │   │ 0 │─────►│ 1 │─────►│ 2 │───►SINK│
  │                          │   └───┘      └───┘      └───┘        │
  │                          │     │  delete  │  insert ▲            │
  │                          │     └──────────┘────────┘             │
  │                          │                                       │
  │                          ├── Viterbi forward pass (O(nodes))     │
  │                          ├── Backtrace: optimal repair sequence  │
  │                          │                                       │
  │                          ▼                                       │
  │  RepairSequence { actions, total_cost, new_pos }                 │
  └──────────────────────────────────────────────────────────────────┘
```

### 4.2 viterbi_multi_step()

`viterbi_multi_step()` (`recovery.rs`:816) implements the full Viterbi
lattice algorithm over the implicit repair lattice:

- **Input:** `token_ids[pos..]`, sync tokens, recovery config
- **Lattice:** `dist[0..=max_lookahead]`, `pred[0..=max_lookahead]`
- **Edge types:** Skip (i→i+1), Delete (i→i+1), Substitute (i→i+1),
  Insert (self-loop, max 1 per position), Sync (i→SINK, cost 0)
- **Beam pruning:** Uses `config.beam_width` (default 3.0)
- **Output:** `RepairSequence` with action list and total cost

The algorithm is mathematically identical to `viterbi_best_path_beam()`
in `lattice.rs`, but operates on fixed-size arrays instead of
`TokenLattice`.

### 4.3 lattice_recovery()

`lattice_recovery()` (`recovery.rs`:1685, feature `context-sensitive-lex`)
bridges token lattices and error recovery:

1. Receives alternative tokenization paths `(Vec<TokenId>, TropicalWeight)`
   from `alternative_paths()` in `lattice.rs`
2. Runs `viterbi_multi_step()` on each alternative
3. Adjusts cost by lexer weight (prefer primary tokenization)
4. Adds a small penalty per alternative tried (0.1 per index)
5. Returns the cheapest successful recovery across all alternatives

This is the only function in the codebase that explicitly connects
`lattice.rs` output to `recovery.rs` input.

### 4.4 EditWeight Integration

`RepairAction::edit_cost()` in `recovery.rs` maps each repair action
to an `EditWeight` value:

| Action     | EditWeight | Semantic                                |
|:-----------|:-----------|:----------------------------------------|
| Skip(n)    | n          | Skip n tokens (1 edit per token)        |
| Delete     | 1          | Remove one unexpected token             |
| Insert     | 2          | Fabricate a missing token               |
| Substitute | 2          | Replace wrong token with correct one    |
| Swap       | 2          | Swap two adjacent tokens                |

This enables future `ProductWeight<TropicalWeight, EditWeight>` lattices
that jointly optimize parse priority and edit distance.

---

## 5. Integration with Composed Dispatch

### 5.1 Weight Maps, Not Lattices

The dispatch subsystem (`dispatch.rs`) uses weight maps, not lattice
objects:

```
BTreeMap<(Category, TokenId), (RuleName, TropicalWeight)>
```

These maps represent "for category C and lookahead token T, dispatch to
rule R with weight W." The dispatch match arms are emitted in
weight-sorted order (lowest weight = highest priority first).

### 5.2 Conceptual Lattice

Conceptually, the dispatch table IS a lattice over (category, token)
pairs:

- Nodes = parse states (category × position in rule)
- Edges = dispatch decisions (token → rule, weighted)
- Viterbi = "pick the best rule for each token"

But this lattice is never materialized as a `TokenLattice` object.

### 5.3 Why TokenLattice Is Not Used

`TokenLattice` is position-oriented (node = input position), while
dispatch is token-oriented (key = (category, token)). The data models
are orthogonal:

| Dimension        | TokenLattice                | Dispatch table          |
|:-----------------|:----------------------------|:------------------------|
| Node semantics   | Input position (char offset)| Grammar category        |
| Edge semantics   | Token + span + weight       | Rule + weight           |
| Query pattern    | "edges from position P"     | "rule for (Cat, Token)" |
| Size             | O(input length)             | O(categories × tokens)  |

Using `TokenLattice` for dispatch would require a mapping layer that
adds complexity without benefit.

---

## 6. Integration with Grammar Composition

### 6.1 No Direct Lattice Use

Grammar composition (`compose.rs`) operates at the `LanguageSpec` level,
merging multiple language definitions into a single spec. It does not
use `TokenLattice` — composition happens before tokenization.

### 6.2 Ambiguities from Composition

When two grammars assign different tokenizations to the same character
sequence, composition can introduce new lexical ambiguities. These
ambiguities flow through the standard WFST pipeline:

1. Composed grammar → merged DFA → multi-accept states
2. Multi-accept states → weighted token alternatives
3. Weighted alternatives → `lex_weighted_core()` output
4. Output → `TokenSource::from_weighted()` → resolution

No special lattice handling is needed at the composition stage.

---

## 7. Integration with NFA Disambiguation

### 7.1 Thread-Local Weight Annotation

The NFA disambiguation system (see
[`08-nfa-wfst-disambiguation.md`](../../design/disambiguation/08-nfa-wfst-disambiguation.md))
uses thread-local variables to annotate spillover alternatives with WFST
weights:

```
AMBIGUOUS_WEIGHTS: Cell<Vec<(Cat, usize, f64)>>
```

When the NFA spills N-1 alternatives (forced-prefix replay), each
alternative carries a tropical weight from `PredictionWfst`. The
`from_alternatives()` tiebreaking logic uses these weights to select
among competing parses.

### 7.2 Spillover as Implicit Lattice

Each NFA spillover can be viewed as an implicit 2-node lattice:

```
  ┌───┐  alt₁(w₁)  ┌───┐
  │ 0 │────────────►│ 1 │
  │   │  alt₂(w₂)  │   │
  │   │────────────►│   │
  │   │  alt₃(w₃)  │   │
  │   │────────────►│   │
  └───┘             └───┘
```

But this "lattice" is never materialized — the alternatives are stored
in a flat `Vec` and the minimum-weight alternative is selected directly.
The overhead is O(N) comparison for N alternatives, which is cheaper
than constructing and running Viterbi on a lattice object.

---

## 8. Integration with Weight Training (wfst-log)

### 8.1 Forward-Backward and Raw Adjacency Lists

`forward_backward.rs` (feature `wfst-log`) computes forward and backward
scores over weighted graphs. It uses raw adjacency lists
`Vec<Vec<(target, weight)>>` rather than `TokenLattice`, because:

1. It operates over **WFST states** (not input positions)
2. Edge labels are `TokenId` (not full `(Token, Range)` pairs)
3. It needs to store both forward (`α`) and backward (`β`) scores
4. The graph structure comes from `PredictionWfst`, not from the lexer

The same Viterbi DP recurrence applies (process nodes in order, relax
outgoing edges), but the type system is different.

### 8.2 Parse Lattice Construction

Weight training (`training.rs`) mentions parse lattice construction as
a planned feature:

> "parse-lattice construction from Pratt parsers is an open research
> problem" (`training.rs`:133)

When implemented, parse lattices would use `TokenLattice` to represent
multiple parse trees for the same input, enabling SGD weight updates
based on oracle vs. predicted parse comparison. This is not yet
implemented.

```
  ┌────────────────────────────────────────────────────────┐
  │  Future training flow (planned, not implemented)       │
  │                                                        │
  │  Input text                                            │
  │    │                                                   │
  │    ▼                                                   │
  │  lex_weighted() → TokenSource::Lattice                 │
  │    │                                                   │
  │    ▼                                                   │
  │  Parse lattice construction (multiple parse trees)     │
  │    │                                                   │
  │    ├── forward_backward() → arc posteriors             │
  │    │                                                   │
  │    ├── Compare: oracle parse vs. predicted parse       │
  │    │                                                   │
  │    ▼                                                   │
  │  SGD weight update → updated PredictionWfst weights    │
  └────────────────────────────────────────────────────────┘
```

---

## 9. Generated Code Anatomy

### 9.1 Lexer Entry Point

The generated code follows this pattern:

```rust
// Generated by PraTTaIL (simplified)
pub fn lex_weighted<'a>(input: &'a str)
    -> Result<Vec<(Token<'a>, Range, f64)>, String>
{
    lex_weighted_with_file_id(input, None)
}

pub fn lex_weighted_with_file_id<'a>(input: &'a str, file_id: Option<u32>)
    -> Result<Vec<(Token<'a>, Range, f64)>, String>
{
    let (mut tokens, eof_pos) = mettail_prattail::runtime_types::lex_weighted_core(
        input, file_id, dfa_next, is_accepting, is_accepting_state,
        accept_token, accept_weight, is_whitespace,
    )?;
    tokens.push((Token::Eof, Range { start: eof_pos, end: eof_pos, file_id }, 0.0));
    Ok(tokens)
}
```

The `accept_weight()` closure maps each DFA accepting state to a
`TropicalWeight` derived from `TokenKind::priority()`.

### 9.2 Currently Always Linear

The generated parser entry point:

```rust
pub fn parse_Cat<'a>(input: &'a str)
    -> Result<Cat, Vec<mettail_prattail::runtime_types::ParseError>>
{
    let weighted = lex_weighted(input)?;
    let source = mettail_prattail::lattice::TokenSource::from_weighted(weighted);
    let tokens = source.resolve().map_err(|e| vec![e.into()])?;
    // ... parse using tokens ...
}
```

Since `from_weighted()` currently always produces `Linear`, and
`resolve()` on `Linear` is identity, the lattice machinery has **zero
runtime overhead** for all current grammars.

### 9.3 Future Context-Sensitive Lexing

When `context-sensitive-lex` is enabled, `from_weighted()` will be
extended to detect multi-token positions and construct `Lattice` variants.
The `resolve()` call will then run Viterbi to extract the best
tokenization. The parser entry point code does not change — only the
internal behavior of `from_weighted()` changes.

---

## 10. Data Flow Summary

```
  ┌─────────────────────────────────────────────────────────────────────┐
  │                     COMPILE TIME                                    │
  │                                                                     │
  │  LanguageSpec                                                       │
  │       │                                                             │
  │       ▼                                                             │
  │  run_pipeline()                                                     │
  │       │                                                             │
  │       ├── extract_from_spec()  → LexerBundle, ParserBundle          │
  │       │                                                             │
  │       ├── generate_lexer_code()                                     │
  │       │   └── Emits: lex_weighted(), accept_weight()                │
  │       │       Types: Vec<(Token<'a>, Range, f64)>                   │
  │       │                                                             │
  │       ├── generate_parser_code()                                    │
  │       │   ├── FIRST/FOLLOW sets                                     │
  │       │   ├── build_prediction_wfsts()                              │
  │       │   │   └── PredictionWfst per category                       │
  │       │   ├── compute_composed_dispatch()                           │
  │       │   │   └── CountingWeight ambiguity warnings                 │
  │       │   ├── Dead-rule detection (BooleanWeight)                   │
  │       │   └── Emits: parse_Cat(), match arms (weight-ordered)       │
  │       │                                                             │
  │       └── Complete: single TokenStream                              │
  │                                                                     │
  ├ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─┤
  │                                                                     │
  │                      RUNTIME                                        │
  │                                                                     │
  │  input: &str                                                        │
  │       │                                                             │
  │       ▼                                                             │
  │  lex_weighted(input)                                                │
  │       │                                                             │
  │       ▼                                                             │
  │  Vec<(Token<'a>, Range, f64)>                                       │
  │       │                                                             │
  │       ▼                                                             │
  │  TokenSource::from_weighted()                                       │
  │       │                                                             │
  │       ├── Linear (always, currently)                                │
  │       │   └── resolve() → identity → Vec<(Token, Range)>           │
  │       │                                                             │
  │       └── Lattice (future: context-sensitive-lex)                   │
  │           └── resolve() → viterbi_best_path() → Vec<(Token, Range)>│
  │                                                                     │
  │       ▼                                                             │
  │  parse_Cat(tokens)                                                  │
  │       │                                                             │
  │       ├── Success → AST                                             │
  │       │                                                             │
  │       └── Error → RecoveryWfst                                      │
  │                   │                                                 │
  │                   ├── viterbi_multi_step()                           │
  │                   │   (implicit repair lattice)                     │
  │                   │                                                 │
  │                   ├── lattice_recovery()‡                           │
  │                   │   (alternative tokenizations from lattice)      │
  │                   │                                                 │
  │                   └── RepairResult → continue parsing               │
  │                                                                     │
  │  ‡ = context-sensitive-lex only                                     │
  └─────────────────────────────────────────────────────────────────────┘
```

---

## 11. Source Map

| Integration concept                 | File                        | Function / Lines            |
|:------------------------------------|:----------------------------|:----------------------------|
| TokenSource enum                    | `src/lattice.rs`            | `TokenSource<T, S>` (51)   |
| TokenLattice struct                 | `src/lattice.rs`            | `TokenLattice<T, S, W>` (240) |
| Viterbi (tropical + beam)           | `src/lattice.rs`            | `viterbi_best_path_beam()` (371) |
| Viterbi (generic semiring)          | `src/lattice.rs`            | `viterbi_generic()` (484)  |
| N-best paths                        | `src/lattice.rs`            | `n_best_paths()` (598)     |
| Alternative paths                   | `src/lattice.rs`            | `alternative_paths()` (708) |
| Implicit repair lattice             | `src/recovery.rs`           | `viterbi_multi_step()` (816) |
| Lattice-aware recovery              | `src/recovery.rs`           | `lattice_recovery()` (1685) |
| RepairAction edit cost              | `src/recovery.rs`           | `RepairAction::edit_cost()` |
| Semiring trait + 6 impls            | `src/automata/semiring.rs`  | `Semiring` (36)             |
| Forward-backward scores             | `src/forward_backward.rs`   | `forward()`, `backward()`  |
| Training (parse lattice, planned)   | `src/training.rs`           | (line 133, planned)         |
| lex_weighted() codegen              | `src/automata/codegen.rs`   | `write_lex_weighted_via_core()` (525) |
| lex_weighted_core() runtime         | `src/runtime_types.rs`      | `lex_weighted_core()` (200+) |
| NFA spillover weights               | `src/dispatch.rs`           | `AMBIGUOUS_WEIGHTS` thread-local |
| Lattice module declaration          | `src/lib.rs`                | `pub mod lattice;` (53)    |

---

## 12. Cross-References

- [Pipeline Integration](pipeline-integration.md) — WFST insertion point in the compile-time pipeline
- [Module Map](module-map.md) — Full module inventory and dependency graph
- [Generated Code Anatomy](../generated-code-anatomy.md) — Annotated walkthrough of generated parser code
- [Data Flow](../data-flow.md) — High-level data flow across PraTTaIL
- [Token Lattice Theory](../../theory/wfst/token-lattices.md) — Formal definitions, proofs
- [Token Lattice Design](../../design/wfst/token-lattices.md) — Implementation decisions, test coverage
- [Error Recovery Design](../../design/wfst/error-recovery.md) — Repair cost model, 3-tier context
- [NFA Disambiguation](../../design/disambiguation/08-nfa-wfst-disambiguation.md) — Forced-prefix replay, weight annotation
- [Weight Training](../../design/wfst/weight-training.md) — LogWeight SGD, forward-backward
