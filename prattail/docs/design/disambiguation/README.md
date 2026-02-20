# PraTTaIL Disambiguation: The Five-Layer Model

## The Disambiguation Problem

Every parser must resolve ambiguity: situations where the same input could legally
produce multiple parse trees. A grammar that says both `1 + 2 * 3 = (1 + 2) * 3`
and `1 + 2 * 3 = 1 + (2 * 3)` is useless until disambiguation rules select exactly
one interpretation.

PraTTaIL resolves ambiguity through **five layered mechanisms**, each targeting a
distinct class of ambiguity. The layers are ordered: earlier layers resolve simpler,
more local ambiguities so that later layers operate on cleaner, pre-disambiguated
input. When a layer cannot fully disambiguate, it passes a structured representation
of the remaining alternatives to the next layer.

## The Five-Layer Stack

```
                    ┌─────────────────────────────────────────┐
                    │  Characters (source text)               │
                    └────────────────┬────────────────────────┘
                                     │
               ┌─────────────────────▼──────────────────────────┐
  Layer 1      │  LEXICAL DISAMBIGUATION                        │
               │  DFA + maximal munch + token priority          │
               │  Resolves: shared prefixes, keyword/ident      │
               │            overlap, token boundaries            │
               └─────────────────────┬──────────────────────────┘
                                     │
                    ┌────────────────▼────────────────────────┐
                    │  Token stream                           │
                    └────────────────┬────────────────────────┘
                                     │
               ┌─────────────────────▼──────────────────────────┐
  Layer 2      │  PARSE PREDICTION                              │
               │  FIRST sets + dispatch tables + lookahead      │
               │  Resolves: which rule to try for a given       │
               │            category, given the next token       │
               └─────────────────────┬──────────────────────────┘
                                     │
                    ┌────────────────▼────────────────────────┐
                    │  Rule selected (prefix handler chosen)  │
                    └────────────────┬────────────────────────┘
                                     │
               ┌─────────────────────▼──────────────────────────┐
  Layer 3      │  OPERATOR PRECEDENCE                           │
               │  Binding power pairs + Pratt loop              │
               │  Resolves: competing infix/prefix/postfix      │
               │            operators, associativity             │
               └─────────────────────┬──────────────────────────┘
                                     │
                    ┌────────────────▼────────────────────────┐
                    │  Expression tree (single category)      │
                    └────────────────┬────────────────────────┘
                                     │
               ┌─────────────────────▼──────────────────────────┐
  Layer 4      │  CROSS-CATEGORY RESOLUTION                     │
               │  FIRST set partition + backtracking dispatch   │
               │  Resolves: token could begin expression in     │
               │            multiple type categories             │
               └─────────────────────┬──────────────────────────┘
                                     │
                    ┌────────────────▼────────────────────────┐
                    │  Typed AST node                         │
                    └────────────────┬────────────────────────┘
                                     │
               ┌─────────────────────▼──────────────────────────┐
  Layer 5      │  ERROR RECOVERY                                │
               │  FOLLOW sets + structural delimiters           │
               │  Resolves: where to resume after a syntax      │
               │            error (prevents error cascades)      │
               └─────────────────────┬──────────────────────────┘
                                     │
                    ┌────────────────▼────────────────────────┐
                    │  AST (possibly with error nodes)        │
                    └─────────────────────────────────────────┘
```

## Layer Summary

| Layer | Ambiguity Class | Mechanism | Example |
|-------|-----------------|-----------|---------|
| **1. Lexical** | Token boundaries and identity | DFA + maximal munch + priority | `==` vs `=` + `=`; `true` vs identifier |
| **2. Prediction** | Which parse rule to apply | FIRST sets + dispatch tables | `(` → grouping vs `42` → literal |
| **3. Precedence** | Operator binding and grouping | Binding power pairs | `1+2*3` → `1+(2*3)` |
| **4. Cross-Category** | Which type category owns a token | FIRST set partition + backtrack | `x` could be `Int` var or `Bool` var |
| **5. Recovery** | Where to resume after error | FOLLOW sets + sync delimiters | Skip to `)` or `;` after bad expression |

## How the Layers Interact

The layers are not independent silos -- they form a pipeline where each layer's
output constrains the next layer's choices. Lexical disambiguation produces tokens
that prediction consumes. Prediction selects a parse rule that the Pratt loop
executes. The Pratt loop may invoke cross-category dispatch when it encounters
a rule referencing a different type category. Error recovery activates only when
an earlier layer fails to find a valid parse. See
[06-layer-interactions.md](06-layer-interactions.md) for end-to-end traces that
show all five layers acting on real input.

## Reading Guide

**If you want to understand a specific layer:**
- Start with the layer's dedicated document (01 through 05)
- Each document is self-contained with worked examples and ASCII diagrams

**If you want to see how layers compose:**
- Read [06-layer-interactions.md](06-layer-interactions.md) for end-to-end traces
- The traces follow input through all five layers, annotating each disambiguation
  decision

**If you want implementation details:**
- Each layer document references exact source files and line numbers
- Cross-references point to the existing deep-dive design and theory documents

**If you are debugging a parse ambiguity:**
- Identify which layer is responsible (use the table above)
- Read that layer's document for the disambiguation rules
- Check [06-layer-interactions.md](06-layer-interactions.md) for interaction effects

## Document Index

| Document | Layer | Lines | Focus |
|----------|-------|-------|-------|
| [01-lexical-disambiguation.md](01-lexical-disambiguation.md) | 1 | ~500 | DFA, maximal munch, priority, equivalence classes |
| [02-parse-prediction.md](02-parse-prediction.md) | 2 | ~450 | FIRST sets, dispatch tables, lookahead, variable fallback |
| [03-operator-precedence.md](03-operator-precedence.md) | 3 | ~500 | Binding power pairs, associativity, three-tier hierarchy |
| [04-cross-category-resolution.md](04-cross-category-resolution.md) | 4 | ~450 | Token partition, backtracking dispatch, cast rules |
| [05-error-recovery.md](05-error-recovery.md) | 5 | ~300 | FOLLOW sets, structural delimiters, panic-mode recovery |
| [06-layer-interactions.md](06-layer-interactions.md) | All | ~600 | End-to-end traces, layer ordering, master flowchart |

## Cross-References to Existing Documentation

Each layer has corresponding deep-dive documentation in the theory and design
directories. The disambiguation documents focus specifically on **how and why
ambiguity is resolved**, complementing the existing docs which teach the mechanisms
themselves.

| Layer | Theory Document | Design Document |
|-------|-----------------|-----------------|
| 1. Lexical | [theory/finite-automata.md](../../../docs/theory/finite-automata.md) §8-9 | [design/automata-pipeline.md](../automata-pipeline.md) §3-8 |
| 2. Prediction | [theory/prediction-and-lookahead.md](../../../docs/theory/prediction-and-lookahead.md) §2-4 | [design/prediction-engine.md](../prediction-engine.md) §2-5 |
| 3. Precedence | [theory/pratt-parsing.md](../../../docs/theory/pratt-parsing.md) §2-5 | [design/pratt-generator.md](../pratt-generator.md) |
| 4. Cross-Category | [theory/prediction-and-lookahead.md](../../../docs/theory/prediction-and-lookahead.md) §5 | [design/cross-category-dispatch.md](../cross-category-dispatch.md) §1-7 |
| 5. Recovery | [theory/prediction-and-lookahead.md](../../../docs/theory/prediction-and-lookahead.md) §3 | [design/prediction-engine.md](../prediction-engine.md) §8 |

## Key Source Files

| File | Layers | Purpose |
|------|--------|---------|
| `prattail/src/automata/mod.rs` | 1 | Token priority system |
| `prattail/src/automata/nfa.rs` | 1 | DAFSA construction, keyword trie |
| `prattail/src/automata/codegen.rs` | 1 | Maximal munch loop, DFA compression |
| `prattail/src/automata/partition.rs` | 1 | Alphabet equivalence classes |
| `prattail/src/prediction.rs` | 2, 4, 5 | FIRST/FOLLOW sets, dispatch, sync predicates |
| `prattail/src/binding_power.rs` | 3 | BP assignment, associativity |
| `prattail/src/pratt.rs` | 3 | Pratt loop, led chain, prefix handlers |
| `prattail/src/dispatch.rs` | 4 | Cross-category dispatch generation |
| `prattail/src/trampoline.rs` | 3, 4 | Stack-safe trampolined versions of layers 3-4 |
