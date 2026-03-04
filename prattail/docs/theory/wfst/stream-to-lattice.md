# Stream-to-Lattice Conversion

> **Quick reference** — A pedagogical guide to how and why PraTTaIL converts
> sequential token streams into lattice-like structures. Read time: 5–10
> minutes.

---

## Table of Contents

1. [Why a Flat Stream Is Insufficient](#1-why-a-flat-stream-is-insufficient)
2. [What Is a Lattice, Intuitively?](#2-what-is-a-lattice-intuitively)
3. [The Seven Conversion Points](#3-the-seven-conversion-points)
4. [The Five Implicit Lattice Structures](#4-the-five-implicit-lattice-structures)
5. [When Does Each Path Activate?](#5-when-does-each-path-activate)
6. [Worked Example: End-to-End](#6-worked-example-end-to-end)
7. [Relationship to Semiring Composition](#7-relationship-to-semiring-composition)
8. [See Also](#8-see-also)

---

## 1. Why a Flat Stream Is Insufficient

A conventional lexer produces a flat sequence of tokens:

```
input:   "float(1 == 1)"
tokens:  [Ident("float"), LParen, Int(1), EqEq, Int(1), RParen]
```

This commits to a single interpretation at lex time. Three classes of
ambiguity make this commitment premature:

### 1.1 Lexical Ambiguity

The input `>>` in a language with both a right-shift operator (`GtGt`) and a
closing generic (`Gt Gt`) produces two valid tokenizations:

```
Interpretation A:  [GtGt]           (shift operator)
Interpretation B:  [Gt, Gt]         (two close-angles)
```

A flat stream must pick one before the parser has context to decide. The wrong
choice forces a parse error and backtrack.

### 1.2 Parse Ambiguity

The input `float(x)` is lexically unambiguous — but syntactically it could be:

```
Interpretation A:  float( x )      (function call: float applied to x)
Interpretation B:  float( x )      (type cast: x cast to float)
```

Both interpretations share the same token stream. The parser needs NFA-level
exploration to discover which interpretations produce a valid AST.

### 1.3 Recovery Ambiguity

When a parse error occurs at position `i`, multiple repair strategies compete:

```
Strategy A:  skip 1 token, sync at ";"       cost = 2.0
Strategy B:  insert ")" before token i       cost = 1.5
Strategy C:  substitute token i with ")"     cost = 3.0
```

Each strategy is an alternative path through a repair lattice. The recovery
system must evaluate all of them to find the minimum-cost repair.

### Core Insight

> A flat stream **commits before context is available**. Lattice structures
> defer the commitment, representing all alternatives simultaneously and
> resolving them when sufficient context exists.

---

## 2. What Is a Lattice, Intuitively?

A **token lattice** is a directed acyclic graph (DAG) where:

- **Nodes** are positions in the input (before/after tokens)
- **Edges** carry a token, a span, and a weight
- **Each source→sink path** is one alternative interpretation

### Three Useful Properties

| Property                    | Meaning                                           | Benefit                              |
|-----------------------------|---------------------------------------------------|--------------------------------------|
| Simultaneous representation | All alternatives coexist in one structure         | No backtracking needed               |
| Weighted selection          | Each edge has a tropical weight (lower = better)  | Principled disambiguation            |
| Linear-time extraction      | Viterbi algorithm finds the best path in O(V + E) | Efficient even for many alternatives |

### Worked Example

For the input `>>` with lexical ambiguity:

```
                        ╭── GtGt (w=0.0) ──╮
     ○ ─────────────────┤                  ├─────── ○
   node 0               ╰── Gt (w=1.0) ─○──╯      node 2
                                       node 1
                                    Gt (w=1.0)
```

- **Path A**: node 0 →[GtGt, w=0.0]→ node 2. Total weight: 0.0
- **Path B**: node 0 →[Gt, w=1.0]→ node 1 →[Gt, w=1.0]→ node 2. Total weight: 2.0

Viterbi selects Path A (weight 0.0 < 2.0). The Tropical semiring's `⊕  = min`
naturally picks the lowest-cost interpretation.

### Explicit vs Implicit Lattices

PraTTaIL uses lattice-like structures in two forms:

| Form         | Structure                                            | Example                                       |
|--------------|------------------------------------------------------|-----------------------------------------------|
| **Explicit** | `TokenLattice<T, S, W>` — full DAG with Viterbi      | `lex_lattice_core()` output                   |
| **Implicit** | Arrays, buffers, or hash maps with lattice semantics | Recovery repair trellis, NFA spillover buffer |

Both encode the same idea: multiple weighted alternatives at a decision point.

---

## 3. The Seven Conversion Points

PraTTaIL has seven places where sequential data becomes lattice-like. They form
a pipeline: each conversion point feeds into the next.

| # | Name                           | Input → Output                                     | Location               | Always-On?                                    |
|---|--------------------------------|----------------------------------------------------|------------------------|-----------------------------------------------|
| 1 | `lex_core()`                   | `&str` → `Vec<(Token, Range)>`                     | `runtime_types.rs:241` | Yes                                           |
| 2 | `lex_weighted_core()`          | `&str` → `Vec<(Token, Range, f64)>`                | `runtime_types.rs:356` | Yes                                           |
| 3 | `lex_lattice_core()`           | `&str` → `TokenSource::Linear` or `::Lattice`      | `runtime_types.rs:482` | Yes (Lattice path unused by current grammars) |
| 4 | `from_weighted()`              | weighted triples → `TokenSource::Linear`           | `lattice.rs:150`       | Yes                                           |
| 5 | `resolve()` / `resolve_beam()` | `TokenSource` → `Vec<(T, S)>` (Viterbi on Lattice) | `lattice.rs:162`       | Yes                                           |
| 6 | `viterbi_multi_step()`         | `[TokenId]` + sync set → `RepairSequence`          | `recovery.rs:1054`     | Yes (on parse error)                          |
| 7 | `from_alternatives()`          | `Vec<Cat>` → single `Cat`                          | `language.rs:289`      | Yes (on NFA ambiguity)                        |

### Reading the Table

**Conversion points 1–3** are lexer-level: they turn raw text into tokens.
Each adds a dimension of lattice capability:

```
lex_core         → flat stream (no weights, no ambiguity)
lex_weighted     → flat stream + weights (WFST annotations)
lex_lattice      → possible lattice (branches at multi-accept states)
```

**Conversion points 4–5** collapse lattice back to flat stream for the parser:

```
from_weighted    → strips weights (backward compat shim)
resolve          → Viterbi extraction (if Lattice) or identity (if Linear)
```

**Conversion points 6–7** are parser-level lattice structures:

```
viterbi_multi_step  → implicit repair trellis on parse error
from_alternatives   → implicit 2-node lattice on NFA ambiguity
```

### Why Seven and Not One?

A single `TokenLattice` for everything would be clean but wasteful. Each
conversion point is optimized for its specific topology:

- Points 1–2 produce flat streams because current grammars never trigger
  lexical ambiguity. Zero overhead.
- Point 6 uses fixed-size arrays because the repair trellis has ≤32 nodes.
  No heap allocation for edges.
- Point 7 uses a `Vec<Cat>` because the "lattice" is always a single fan-out:
  one source, N alternatives, one sink. A full DAG would be overkill.

---

## 4. The Five Implicit Lattice Structures

Five places in PraTTaIL use lattice semantics without instantiating
`TokenLattice`. Each is optimized for its specific shape.

| # | Structure                  | Representation                         | Lattice Shape                | Why Not `TokenLattice`?                       |
|---|----------------------------|----------------------------------------|------------------------------|-----------------------------------------------|
| A | Recovery repair trellis    | `Vec<RecoveryCost>` arrays             | Forward trellis (≤32 nodes)  | Fixed topology, arrays faster                 |
| B | NFA spillover buffer       | `Cell<Vec<(Cat, usize, f64)>>`         | 2-node lattice with N edges  | Single branching point                        |
| C | Dispatch weight maps       | `HashMap<(Cat, TokenId), Vec<Action>>` | Per-token fan-out            | Compile-time only, never traversed at runtime |
| D | Forward-backward adjacency | `Vec<Vec<(usize, W)>>`                 | Generic DAG over WFST states | Different node semantics (states ≠ positions) |
| E | WFST transitions           | `Vec<WfstState>`                       | Full automaton DAG           | Automaton semantics, not token sequences      |

### A. Recovery Repair Trellis

```
Nodes:     0     1     2     3    SINK
           ┃     ┃     ┃     ┃     ┃
 skip(2.0) ┠─────►     ┃     ┃     ┃
 del(3.0)  ┠─────►     ┃     ┃     ┃
 sub(3.0)  ┠─────►     ┃     ┃     ┃
 ins(1.5)  ┠─────────────────────────►
           ┃ skip(2.0) ┃     ┃     ┃
           ┃     ┠─────►     ┃     ┃
           ┃     ┃ sync(0)   ┃     ┃
           ┃     ┠───────────────────►
```

Each node `i` is a token position after the error. Edges are repair actions with
costs. The Viterbi forward pass finds the minimum-cost repair path to SINK.
This is a **forward trellis** — edges only go left-to-right (or to SINK).

### B. NFA Spillover Buffer

```
                    ╭── Alt₁ (w=0.3) ──╮
     parse point ───┤── Alt₂ (w=0.5) ──├─── continue
                    ╰── Alt₃ (w=0.8) ──╯
```

A single branching point with N alternatives, each carrying a parse result, end
position, and tropical weight. The replay loop drains alternatives in weight
order and short-circuits on the first accepting result.

### C–E: Compile-Time and Training Structures

Structures C–E exist at compile time or during weight training. They never
participate in runtime token processing:

- **C** (Dispatch weight maps): Constructed during pipeline codegen, baked into
  generated `match` arms. The "lattice" is the set of possible dispatch
  actions for each (category, token) pair.
- **D** (Forward-backward adjacency): Raw `Vec<Vec<(usize, W)>>` adjacency
  lists used by `forward_scores()` and `backward_scores()` in
  `forward_backward.rs`. Nodes are WFST states, not input positions.
- **E** (WFST transitions): The `PredictionWfst` automaton itself, with
  `Vec<WfstState>` containing `Vec<WeightedTransition>`. This is the
  source of compile-time weights baked into generated code.

---

## 5. When Does Each Path Activate?

The following decision tree traces the runtime flow from input string to AST.
Feature gates are annotated where applicable.

```
                         Input string
                              │
                    ┌─────────┴─────────┐
                    │   Generated lex() │
                    └─────────┬─────────┘
                              │
              ┌───────────────┼───────────────┐
              ▼               ▼               ▼
         lex_core ①    lex_weighted ②   lex_lattice ③
         (unweighted)   (+ weights)     (+ alternatives)
              │               │               │
              │          from_weighted ④      │
              │          (strip weights)      │
              ▼               ▼               │
              └───────┬───────┘          resolve ⑤
                      │                  (Viterbi)
                      ▼                       │
                      └──────────┬────────────┘
                                 ▼
                          Vec<(Token, Range)>
                                 │
                    ┌────────────┴────────────┐
                    │      Parser (RD/Pratt)  │
                    └────────────┬────────────┘
                                 │
                    ┌────── parse OK? ──────┐
                    ▼                       ▼
                   yes                      no
                    │                       │
                    │            viterbi_multi_step ⑥
                    │            (repair trellis)
                    │                       │
                    │              repair + re-parse
                    │                       ▼
                    └──────────┬────────────┘
                               │
                    ┌──── NFA ambiguity? ────┐
                    ▼                        ▼
                    no                      yes
                    │                        │
                    │           from_alternatives ⑦
                    │           (weight tiebreak)
                    │                        ▼
                    └──────────┬─────────────┘
                               ▼
                              AST
```

### Feature Gate Summary

| Conversion Point                 | Feature Gate     | Status                                    |
|----------------------------------|------------------|-------------------------------------------|
| ① `lex_core()`                   | None (always-on) | Active in all grammars                    |
| ② `lex_weighted_core()`          | None (always-on) | Active in all grammars                    |
| ③ `lex_lattice_core()`           | None (always-on) | Compiled but Lattice path never triggered |
| ④ `from_weighted()`              | None (always-on) | Backward-compat shim                      |
| ⑤ `resolve()` / `resolve_beam()` | None (always-on) | Linear path = identity                    |
| ⑥ `viterbi_multi_step()`         | None (always-on) | Triggered on parse error                  |
| ⑦ `from_alternatives()`          | None (always-on) | Triggered on NFA ambiguity                |
| Forward-backward                 | `wfst-log`       | Training only                             |

---

## 6. Worked Example: End-to-End

Trace the input `float(1 == 1)` through the RhoCalc grammar, which has both
a `float()` cast rule and function-call syntax.

### Step 1: Lexing (Conversion Point ②)

`lex_weighted_core()` produces a flat weighted stream:

```
Token          Range        Weight
──────────────  ───────────  ──────
Ident("float")  0:0–0:5      0.0
LParen          0:5–0:6      0.0
Int(1)          0:6–0:7      0.0
EqEq            0:8–0:10     0.0
Int(1)          0:11–0:12    0.0
RParen          0:12–0:13    0.0
```

No lexical ambiguity — all weights are 0.0.

### Step 2: Weight Stripping (Conversion Point ④)

`from_weighted()` strips weights → `TokenSource::Linear`.

### Interlude: Where Do Dispatch Weights Come From?

Step 1 showed all lex weights at 0.0 — the input is lexically unambiguous.
But Step 3 (below) introduces non-zero **dispatch weights** that determine
which parse interpretation wins. These are a separate weight system:

| Weight System   | Source                    | When Assigned           | Purpose           | Example                           |
|-----------------|---------------------------|-------------------------|-------------------|-----------------------------------|
| Lex weight      | `from_priority()`         | Runtime (DFA)           | Lexical ambiguity | 0.0 (all tokens unambiguous here) |
| Dispatch weight | Specificity + action type | Compile time (pipeline) | Parse ambiguity   | 0.40 (FloatCast)                  |

**Dispatch weight formula.** Each rule's weight is:

```
w_final = w_action + w_specificity        (tropical ⊗  = addition)
```

**Action type weight** (`wfst.rs:1264–1286`):

| Action Type                 | w_action | Rationale                                       |
|-----------------------------|----------|-------------------------------------------------|
| Direct                      | 0.0      | Deterministic, no backtracking                  |
| Grouping                    | 0.0      | Delimiter-driven                                |
| CrossCategory (no backtrack)| 0.0      | Deterministic cross-category                    |
| CrossCategory (backtrack)   | 0.5      | Speculative try, may fail                       |
| Cast                        | 0.5      | Cross-category type coercion validation         |
| Lookahead                   | 1.0 + k  | Each extra lookahead token adds cost            |
| Variable                    | 2.0      | Pure wildcard, matches anything                 |

**Rule specificity weight** (`prediction.rs:1671–1692`):

```
w_specificity = 1 / (1 + terminals + 0.5 × nonterminals)
```

**Theoretical rationale.**

*Specificity as inverse structural entropy.* A grammar rule constrains the
language it accepts. More terminal symbols means more fixed constraints, fewer
accepted strings, and lower structural entropy. The formula `1/(1 + structure)`
is a monotone decreasing function mapping structural complexity to weight: the
more constrained a rule, the lower its weight, and therefore the higher its
priority under tropical `⊕  = min`. A keyword-driven rule like `float(Expr)` is
more informative than generic `Ident(Args)` because the keyword eliminates an
entire space of possible interpretations.

*Terminal/nonterminal asymmetry.* Terminals count 1.0 because each terminal is
a fixed constraint — it matches exactly one token class, deterministically
reducing the language. Nonterminals count 0.5 because each nonterminal is a
free variable admitting any derivation of the referenced category. The 2:1
ratio reflects this asymmetry. The `1 +` base in the denominator ensures
epsilon productions get weight 1.0 (maximum, least specific) and that the
weight is always in (0, 1].

*Action type as parsing effort cost.* Action type weights encode the
computational cost of the dispatch mechanism — a separate axis from specificity.
Direct dispatch has zero overhead; backtracking and wildcards incur measurable
cost. These compose additively under tropical ⊗  because Bellman's principle
guarantees that the optimal multi-step dispatch path minimizes accumulated
weight (see [Optimization Theory](../foundations/06-optimization-theory.md) §1).

> For the full specificity formula derivation, see
> [Rule Specificity Weights](semirings.md#17-rule-specificity-weights).
> For the Bellman composition guarantee, see
> [Optimization Theory](../foundations/06-optimization-theory.md) §1.

### Step 3: Parsing with NFA Ambiguity

The parser encounters `float` at the dispatch point for category `Expr`. Two
NFA alternatives exist:

| Alt | Rule | Structure | w_specificity | w_action | w_final |
|-----|------|-----------|---------------|----------|---------|
| Alt₁ | `FloatCast: float( Expr )` | 1 term + 1 NT | 1/(1+1.5) = 0.40 | 0.0 (Direct) | **0.40** |
| Alt₂ | `FunctionCall: Ident( Args )` | 1 term + 1.5 NT | 1/(1+1.75) ≈ 0.36 | 0.5 (CrossCat+backtrack) | **≈ 0.86** |

FloatCast wins on both axes: its keyword gives it slightly higher structural
specificity (0.40 vs 0.36 — note that lower specificity weight means *more*
specific), and its direct dispatch avoids the backtracking penalty (0.0 vs 0.5).

Both are tried. Weights are stored in `AMBIGUOUS_WEIGHTS`.

### Step 4: NFA Spillover (Implicit Lattice B)

The trampoline parser tries Alt₁ (weight-best) as primary. Alt₂ is pushed to
`NFA_PREFIX_SPILL_EXPR`:

```
spillover = [(FunctionCall(float, [EqExpr(1, 1)]), pos=13, w≈0.86)]
```

### Step 5: Disambiguation (Conversion Point ⑦)

`from_alternatives()` receives both results:

```
                    ╭── FloatCast(EqExpr(1,1))    w=0.40  accepting ──╮
  parse point ──────┤                                                 ├── result
                    ╰── FunctionCall(float,[...])  w≈0.86  accepting ──╯
```

Both are accepting. Stage 2 tiebreaks on WFST weight:

```
argmin_weight(accepting_alternatives):
  Alt₁ (FloatCast):     w = 0.40
  Alt₂ (FunctionCall):  w ≈ 0.86
  ⊕ = min(0.40, 0.86) = 0.40 → Alt₁ wins
```

**Result**: `FloatCast(EqExpr(Int(1), Int(1)))` — the `1 == 1` is parsed as an
equality expression inside a float cast.

### Lattice Diagram at the NFA Level

```
              FloatCast         w = 0.40
             ╭──────────────────────────╮
  ○ input ───┤                          ├─── ○ result
             ╰──────────────────────────╯
              FunctionCall      w ≈ 0.86
```

This is the implicit 2-node lattice (Structure B from §4). The "Viterbi" here
is simply `min_by(weight)` — the degenerate case of Viterbi on a graph with
only parallel edges.

---

## 7. Relationship to Semiring Composition

The stream-to-lattice conversion points are **consumers** of semiring
operations. The [semiring composition framework](semiring-composition.md)
defines three modes of semiring interaction; each lattice structure participates
in one or more:

| Lattice Structure          | Semiring Mode              | Operation                                      |
|----------------------------|----------------------------|------------------------------------------------|
| `TokenLattice` (explicit)  | Mode 1 (Re-Interpretation) | TropicalWeight → Viterbi extraction            |
| Recovery repair trellis    | Mode 2 (ProductWeight)     | `ProductWeight<Tropical, Edit>` joint tracking |
| NFA spillover buffer       | Mode 3 (Cross-Structure)   | WFST weights → semantic disambiguation         |
| Forward-backward adjacency | Mode 1                     | LogWeight → total probability (training)       |
| WFST transitions           | Mode 1                     | TropicalWeight → best-action selection         |

### How the Modes Map to Conversion Points

- **Mode 1** (Re-Interpretation): Conversion points ⑤ (`resolve`) and the
  forward-backward algorithm operate over existing lattice structures,
  reinterpreting edge weights under different semirings.

- **Mode 2** (ProductWeight): Conversion point ⑥ (`viterbi_multi_step`) uses
  `RecoveryCost = ProductWeight<TropicalWeight, EditWeight>` to jointly
  minimize cost and track edit operations.

- **Mode 3** (Cross-Structure Data Flow): Conversion point ⑦
  (`from_alternatives`) receives WFST weights via thread-local channels
  (`AMBIGUOUS_WEIGHTS`) and uses them for semantic disambiguation. The weights
  originate from compile-time WFST construction (Structure E) and flow into
  runtime parse disambiguation.

---

## 8. See Also

### Token Lattice Documentation (Theory / Design / Architecture)

- [Token Lattices — Theory](token-lattices.md): Formal definitions (DAG,
  Viterbi, beam pruning), proofs, complexity analysis
- [Token Lattices — Design](../../design/wfst/token-lattices.md):
  `TokenSource` enum, generic parametrization, implementation decisions
- [Token Lattices — Architecture](../../architecture/wfst/token-lattices.md):
  Pipeline integration points, generated code anatomy, data flow

### Stream-to-Lattice Architecture

- [Stream-to-Lattice — Architecture](../../architecture/wfst/stream-to-lattice.md):
  Code-path walkthrough with source-line references for all seven conversion
  points and five implicit structures

### Related WFST Documentation

- [Semirings](semirings.md): Semiring axioms, all concrete weight types
- [Semiring Composition](semiring-composition.md): Three modes of
  multi-semiring interaction
- [Viterbi and Forward-Backward](viterbi-and-forward-backward.md): Full
  algorithm details and proofs
- [NFA Spillover Architecture](../../architecture/wfst/nfa-spillover-architecture.md):
  Demand-driven replay, weight-threshold pruning
- [Error Recovery Design](../../design/wfst/error-recovery.md): Recovery WFST
  construction, repair cost model, 3-tier context
