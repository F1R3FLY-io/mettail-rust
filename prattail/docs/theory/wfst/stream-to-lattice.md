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
6. [Weight Assignment Methods](#6-weight-assignment-methods)
7. [Worked Example: End-to-End](#7-worked-example-end-to-end)
8. [Relationship to Semiring Composition](#8-relationship-to-semiring-composition)
9. [See Also](#9-see-also)

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
     parse point ───┼── Alt₂ (w=0.5) ──┼─── continue
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

## 6. Weight Assignment Methods

PraTTaIL assigns weights to lattice edges, dispatch alternatives, and repair
actions using **14 distinct methods** across **10 semiring types**. These
methods span three lifecycle phases: compile-time pipeline processing (A1–A9),
runtime parsing and recovery (B1–B5), and offline weight training (C1–C2).

### Taxonomy

| Phase        | # Methods | Semirings Used                                                                              |
|--------------|-----------|---------------------------------------------------------------------------------------------|
| Compile-time | 9         | TropicalWeight, CountingWeight, BooleanWeight, ContextWeight, ComplexityWeight, NbestWeight |
| Runtime      | 5         | TropicalWeight, EditWeight, ProductWeight, any W: Semiring                                  |
| Training     | 2         | LogWeight, EntropyWeight                                                                    |

### Lifecycle Diagram

```
                  ┌───────────────────────────────────────────────────┐
                  │                    Compile Time                   │
                  │                                                   │
Grammar DSL ────► │  Pipeline: A1–A9                                  │
                  │  ┌─────┐ ┌─────┐ ┌─────┐ ┌─────┐ ┌─────┐ ┌─────┐  │
                  │  │ A1  │ │ A2  │ │ A3  │ │ A5  │ │ A6  │ │ A7  │  │
                  │  │Prio │ │Act  │ │Spec │ │Count│ │Reach│ │Ctx  │  │
                  │  └──┬──┘ └──┬──┘ └──┬──┘ └──┬──┘ └──┬──┘ └──┬──┘  │
                  │     └───┬───┘       │       │       │       │     │
                  │    A4 Compose       │    ┌──┴──┐ ┌──┴──┐ ┌──┴──┐  │
                  │    w_action+w_spec  │    │ A8  │ │ A9  │ │diag │  │
                  │         │           │    │Cmplx│ │Nbest│ │     │  │
                  │         ▼           │    └──┬──┘ └──┬──┘ └──┬──┘  │
                  │    Generated Code ◄─┘       ▼       ▼       ▼     │
                  │                          Diagnostics              │
                  └─────────┊─────────────────────────────────────────┘
                            │
                  ┌─────────┊─────────────────────────────────────────┐
                  │         ▼              Runtime                    │
                  │                                                   │
                  │  Parser: B1–B5                                    │
                  │  ┌─────┐ ┌─────┐ ┌─────┐ ┌─────┐ ┌─────┐          │
                  │  │ B1  │ │ B2  │ │ B3  │ │ B4  │ │ B5  │          │
                  │  │Repai│ │Edit │ │Dual │ │Ident│ │Pos  │          │
                  │  └──┬──┘ └──┬──┘ └──┬──┘ └──┬──┘ └──┬──┘          │
                  │     └───┬───┘       │       │       │             │
                  │     Recovery        │    Lattice  NFA disambig    │
                  │         │           │       │       │             │
                  │         ▼           ▼       ▼       ▼             │
                  │                    AST                            │
                  │                     │                             │
                  │           WEIGHT_CORRECTIONS                      │
                  └─────────────────────┊─────────────────────────────┘
                                        │
                  ┌─────────────────────┊──────────────────────────────┐
                  │                     ▼       Training (wfst-log)    │
                  │  ┌─────┐ ┌─────┐                                   │
                  │  │ C1  │ │ C2  │                                   │
                  │  │ Log │ │Entro│                                   │
                  │  └──┬──┘ └──┬──┘                                   │
                  │     └───┬───┘                                      │
                  │         ▼                                          │
                  │   Retrained Weights ─ ─ ─► Compile Time            │
                  └────────────────────────────────────────────────────┘
```

---

### 6.1 Compile-Time Methods (Pipeline)

#### 6.1.1 Lexical Priority Mapping (A1)

**Semiring**: TropicalWeight

**Formula**:

> w = 10.0 − p, where p ∈ {0, 1, 2, …, 10} is the token's `priority()` value.

The function `priority()` is a method on `TokenKind` (`automata/mod.rs:62`) that
returns a `u8` disambiguation priority for each token class. Higher values
indicate more specific (less ambiguous) token kinds. The weight conversion
`TropicalWeight::from_priority(p)` computes `10.0 − p` (`semiring.rs:101`).

Higher priority (larger `p`) maps to lower weight (better under tropical
`⊕  = min`). The constant `MAX_PRIORITY = 10` ensures all weights are
non-negative.

**Priority-to-weight table**:

| Token Class | Priority (p) | Weight (w) | Rationale                           |
|-------------|:------------:|:----------:|-------------------------------------|
| Keywords    |      10      |    0.0     | Exact match, zero ambiguity         |
| Operators   |     8–9      |  1.0–2.0   | Fixed symbols, low ambiguity        |
| Literals    |     5–7      |  3.0–5.0   | Pattern-matched, moderate ambiguity |
| Ident       |      1       |    9.0     | Wildcard, high ambiguity            |

**Rationale.** Keywords and operators are deterministic lexical anchors: they
match exactly one token class and eliminate entire branches of the parse search
space. Identifiers, by contrast, are lexical wildcards — `float` is
simultaneously `KwFloat` (keyword, p=10) and `Ident` (identifier, p=1). The
priority-to-weight mapping ensures the keyword interpretation (w=0.0) is always
preferred over the identifier interpretation (w=9.0) in any tropical
shortest-path computation.

The function `accept_weight(state: u32) -> f64` is generated per-grammar by
`write_accept_weight_arms()` (`codegen.rs:480`). It returns the tropical weight
for the highest-priority token kind accepted at the given DFA state, or
`f64::INFINITY` (tropical zero) for non-accepting states. At runtime, it is
passed as a closure to `lex_weighted_core()` (`runtime_types.rs:356`).

**Example.** In the Calculator grammar, the input `float` at a multi-accept
DFA state produces:

```
    DFA state 17 ──► accept_weight(17)      [generated: codegen.rs:564]
      KwFloat (priority 10) → w = 10.0 − 10 = 0.0  ← selected
      Ident   (priority  1) → w = 10.0 −  1 = 9.0
```

**Source**: `semiring.rs:101–103`

#### 6.1.2 Action Type Weight (A2)

**Semiring**: TropicalWeight

**Formula**: Fixed table mapping `DispatchAction` variant to weight:

| Action Type                  | w_action | Rationale                           |
|------------------------------|:--------:|-------------------------------------|
| Direct                       |   0.0    | Deterministic, no backtracking      |
| Grouping                     |   0.0    | Delimiter-driven, deterministic     |
| CrossCategory (no backtrack) |   0.0    | Deterministic cross-category        |
| CrossCategory (backtrack)    |   0.5    | Speculative try, may fail and retry |
| Cast                         |   0.5    | Cross-category type coercion        |
| Lookahead                    | 1.0 + k  | k = lookahead order (extra tokens)  |
| Variable                     |   2.0    | Pure wildcard, matches anything     |

**Rationale.** Action type weights encode the **parsing effort cost** — the
computational overhead of the dispatch mechanism itself. This is a separate
axis from specificity (A3). Direct dispatch resolves in O(1) with zero
backtracking; backtracking cross-category dispatch may require a full
speculative parse attempt that fails; variable dispatch accepts any token
unconditionally but provides no structural information. The weights are
ordered by expected parsing cost, and they compose additively under tropical
`⊗  = +` because Bellman's principle guarantees that the optimal multi-step
dispatch path minimizes accumulated weight (see
[Optimization Theory](../foundations/06-optimization-theory.md) §1).

**Example.** In RhoCalc, the token `float` at the `Proc` dispatch point:

```
    FloatCast:   DispatchAction::Direct { .. }    → w_action = 0.0
    FuncCall:    DispatchAction::CrossCategory { needs_backtrack: true, .. }
                                                  → w_action = 0.5
```

**Source**: `wfst.rs:1264–1286`

#### 6.1.3 Rule Specificity Weight (A3)

**Semiring**: TropicalWeight

**Formula**:

> w_specificity = 1 / (1 + t + 0.5n)
>
> where t = number of terminal items, n = number of nonterminal items
> (Ident items count as 0.5 nonterminals).

**Rationale (specificity as inverse structural entropy).** A grammar rule
constrains the language it accepts. More terminal symbols means more fixed
constraints, fewer accepted strings, and lower structural entropy. The formula
`1/(1 + structure)` is a monotone decreasing function mapping structural
complexity to weight: the more constrained a rule, the lower its weight, and
therefore the higher its priority under tropical `⊕  = min`.

*Terminal/nonterminal asymmetry.* Terminals count 1.0 because each terminal is
a fixed constraint — it matches exactly one token class, deterministically
reducing the language. Nonterminals count 0.5 because each nonterminal is a
free variable admitting any derivation of the referenced category. The 2:1
ratio reflects this asymmetry. The `1 +` base in the denominator ensures
epsilon productions get weight 1.0 (maximum, least specific) and that the
weight is always in (0, 1].

*Ident items.* An `Ident` in the rule's FIRST set counts as 0.5 nonterminals
rather than 1.0 terminal, because `Ident` is a lexical wildcard that matches
any identifier string — it provides less structural constraint than a fixed
keyword but more than a full nonterminal category.

**Example.** In RhoCalc:

```
    FloatCast: float( Expr )
      t = 1 (KwFloat), n = 1 (Expr)
      specificity = 1 + 0.5×1 = 1.5
      w_specificity = 1/(1 + 1.5) = 1/2.5 = 0.40

    FunctionCall: Ident( Args )
      t = 1 (LParen — counted from FIRST items), n_ident = 0.5, n_nt = 1 (Args)
      specificity = 1 + 0.5×1.5 = 1.75
      w_specificity = 1/(1 + 1.75) = 1/2.75 ≈ 0.36
```

Note: lower `w_specificity` means *more* specific. `FunctionCall` has slightly
lower specificity weight (0.36 vs 0.40) because it has more structural items,
but it loses on action type weight (A2).

**Source**: `prediction.rs:1685–1701`

#### 6.1.4 Dispatch Weight Composition (A4)

**Semiring**: TropicalWeight

**Formula**:

> w_final = w_action ⊗  w_specificity = w_action + w_specificity

The final dispatch weight for a rule is the tropical product (addition) of its
action type weight (A2) and its specificity weight (A3). This is the weight
baked into generated `match` arms and stored in `AMBIGUOUS_WEIGHTS` for NFA
disambiguation.

**Rationale.** Tropical `⊗  = +` decomposes the total dispatch cost into two
independent axes: *mechanism cost* (how expensive is the dispatch path?) and
*structural cost* (how specific is the rule?). Additivity ensures that the
composed weight respects Bellman's optimality principle: the best composed
weight is the one that minimizes the sum of both components.

**Example.** Continuing from A2 and A3:

```
    FloatCast:    w = 0.0 + 0.40 = 0.40
    FunctionCall: w = 0.5 + 0.36 ≈ 0.86
```

FloatCast wins because its zero action cost more than compensates for its
slightly higher specificity weight.

**Source**: `prediction.rs:1546`

#### 6.1.5 Derivation Counting (A5)

**Semiring**: CountingWeight

**Formula**:

> count = |{r ∈ Rules(C) : token ∈ FIRST(r)}|

For each (category, token) pair, the derivation count is the number of grammar
rules in category `C` whose FIRST set contains the given token. The count is computed by
`PredictionWfst::predict_with_confidence(&self, token_name: &str)`
(`wfst.rs:362`), which returns `Vec<(&WeightedAction, CountingWeight)>` —
each dispatch action paired with the total number of alternatives.

**Interpretation**:

| Count | Meaning                                     | Diagnostic Action       |
|:-----:|---------------------------------------------|-------------------------|
|   0   | Dead dispatch (no rule handles this token)  | Dead-rule warning       |
|   1   | Unambiguous dispatch                        | Deterministic arm       |
|  > 1  | Ambiguous dispatch (NFA exploration needed) | Ambiguity warning (W05) |

**Example.** In RhoCalc, the token `Ident` in category `Proc`:

```
    PInput:  Ident ∈ FIRST(PInput)   ✓
    POutput: Ident ∈ FIRST(POutput)  ✓
    PQuote:  Ident ∉ FIRST(PQuote)   ✗
    ───────────────────────────────────
    count = CountingWeight(2)
```

Two rules compete for `Ident` in `Proc`, triggering NFA merged-prefix dispatch.

**Source**: `wfst.rs:362–366`

#### 6.1.6 Reachability Analysis (A6)

**Semiring**: BooleanWeight

**Formula**:

> reachable(C) = ∃ path from root category to C via FIRST + cross-cat + cast edges

Category reachability is computed as a fixed-point over the category graph
using BooleanWeight, where `⊕  = ∨` (OR) and `⊗  = ∧` (AND). A category is
reachable if it has a non-empty FIRST set or is transitively reachable from a
reachable category via cross-category or cast edges. A rule is dead (Tier 2)
if its entire category is unreachable.

**Reachability graph** (small example):

```
    Expr ──cross-cat──► Proc ──cast──► Name
     │                                  │
     └────────cross-cat─────────────────┘
                                        ╳
                                   Unreachable
                                  (no inbound edges)
```

In the example above, `Unreachable` is a category with no inbound edges from
any reachable category, so `reachable(Unreachable) = false` and all its rules
receive dead-rule warnings.

The companion analysis
`detect_nearly_dead_paths(rule_infos, categories, first_sets)`
(`pipeline.rs:450`) extends this with
`ProductWeight<BooleanWeight, CountingWeight>` to jointly compute reachability
*and* derivation counts in a single forward-backward pass, identifying paths
that are technically reachable but carry negligible derivation flow.

**Source**: `pipeline.rs:141`

#### 6.1.7 Rule Context Tracking (A7)

**Semiring**: ContextWeight

**Formula**:

> context(s) = ⊕{singleton(label_i) : transition_i reaches s}

The function `singleton(id)` is `ContextWeight::singleton(label_id: u8) -> Self`
(`semiring.rs:654`), which returns a `u128` bitset with exactly bit `label_id`
set: `ContextWeight(1u128 << label_id)`.

Here `⊕  = ∪` (bitwise OR over 128-bit bitsets). Each rule label is assigned a
unique bit position (0–127). When a WFST state is reachable by transitions
from multiple rules, its ContextWeight accumulates all contributing rule labels.

**Capacity**: 128 distinct rule labels per grammar (sufficient for all current
PraTTaIL grammars). The bitset representation is `Copy` and allocation-free.

**Example.** A WFST state `s₃` reachable by PInput (bit 3) and POutput
(bit 5):

```
    singleton(3) = 0b...001000
    singleton(5) = 0b...100000
    context(s₃) = 0b...001000 ⊕  0b...100000 = 0b...101000
    count = context(s₃).count_ones() = 2
```

A context count of 1 means the state is unambiguous (single rule). A count > 1
identifies states that participate in multiple rules, helping diagnose
structural overlap in the grammar.

**Source**: `semiring.rs:654`

#### 6.1.8 Lookahead Bottleneck (A8)

**Semiring**: ComplexityWeight

**Formula**:

> bottleneck(path) = ⊗{complexity(arc_i)} = max(complexity_i)

where `complexity(arc)` extracts the `ComplexityWeight` value from arc — the
lookahead depth required at that dispatch point — and `⊗  = max` is the
tropical-max semiring on non-negative integers (dual to the standard tropical
semiring). Lookahead depth is assigned via `ComplexityWeight` constructors
(`semiring.rs:798–817`):

| Constructor              | Value      | Meaning                            |
|--------------------------|:----------:|------------------------------------|
| `deterministic()`        |     0      | No ambiguity, single rule          |
| `single_lookahead()`     |     1      | Two alternatives, 1-token resolve  |
| `multi_lookahead(k)`     |     k      | k-token lookahead required         |
| `infinite()`             | `u32::MAX` | Dead/unreachable dispatch point    |

Per-group complexity is computed by `compute_group_complexity()`
(`trampoline.rs:132`) as `|rules| × max_depth`. The bottleneck complexity of a
path is the maximum over all arc complexities.

**Rationale.** The bottleneck complexity identifies the hardest dispatch point
along any path — the point requiring the deepest lookahead. Paths with lower
bottleneck are preferred because they make fewer speculative parsing decisions.

**Example.** A dispatch path through three WFST arcs:

```
    arc₁: deterministic     → complexity = 0
    arc₂: 2-token lookahead → complexity = 2
    arc₃: deterministic     → complexity = 0
    ─────────────────────────────────────────
    bottleneck = max(0, 2, 0) = ComplexityWeight(2)
```

**Source**: `semiring.rs:810–812`

#### 6.1.9 N-Best Path Tracking (A9)

**Semiring**: NbestWeight\<N\>

**Formula**:

> top_N = merge(A, B): two-pointer merge of sorted entry lists,
> deduplicate by `path_id`, keep the N entries with lowest weight.

Each `NbestEntry` is a `(path_id: u32, weight: TropicalWeight)` pair.
The `⊕` operation merges two N-best lists, and `⊗` extends paths by weight
accumulation.

**Confidence gap**:

> Δ = w₂ − w₁

The weight difference between the best and second-best entries measures
disambiguation confidence. A large gap means the best path is significantly
better; a small gap indicates near-ambiguity.

**Example** (N=2):

```
    NbestWeight { entries: [(path_0, w=0.3), (path_1, w=1.7)] }
    confidence_gap = 1.7 − 0.3 = 1.4  → high confidence

    NbestWeight { entries: [(path_0, w=0.3), (path_1, w=0.35)] }
    confidence_gap = 0.35 − 0.3 = 0.05  → near-ambiguous
```

Returns `f64::INFINITY` if fewer than 2 entries exist (single or no
alternative = infinite confidence).

**Source**: `semiring.rs:1437–1441, 1487`

---

### 6.2 Runtime Methods (Parser)

#### 6.2.1 Recovery Repair Costs (B1)

**Semiring**: TropicalWeight

**Base cost table**:

| Repair Action | Base Cost | Rationale                                      |
|---------------|:---------:|------------------------------------------------|
| Skip          | 0.5/token | Cheapest: consume and discard unexpected input |
| Delete        |    1.0    | Remove one token from the stream               |
| Swap          |   1.25    | Reorder two adjacent tokens                    |
| Substitute    |    1.5    | Replace wrong token with expected one          |
| Insert        |    2.0    | Fabricate a missing token (most expensive)     |

**Context multipliers** (3-tier system):

| Tier | Context Signal          | Multiplier        | Effect                                          |
|------|-------------------------|-------------------|-------------------------------------------------|
| 1    | Deep nesting (> 1000)   | skip × 0.5        | Discount skip in deeply nested constructs       |
| 1    | Shallow depth (< 10)    | skip × 2.0        | Penalize skip at top level                      |
| 1    | Low binding power (< 4) | skip × 0.75       | Slight skip discount for loose operators        |
| 1    | Collection frame        | insert × 0.5      | Encourage insertion in lists/arrays             |
| 1    | Group frame             | insert × 0.5      | Encourage insertion for balanced delimiters     |
| 1    | Unmatched bracket       | insert × 0.3      | Strongly encourage bracket insertion            |
| 1    | Mixfix frame            | substitute × 0.75 | Favor substitution in ternary operators         |
| 3    | Simulation succeeds     | cost × 0.5        | Reward repairs that lead to valid continuations |
| 3    | Simulation fails        | cost + 0.2/token  | Penalize repairs that lead to more errors       |

**Adaptive recovery** (B2 extension):

| Parse Confidence     | Condition            | Adjustment                     |
|----------------------|----------------------|--------------------------------|
| Deterministic regime | running_weight < 1.0 | skip × 0.75 (confident → skip) |
| Ambiguous regime     | running_weight ≥ 1.0 | insert × 0.5 (unsure → insert) |

**Worked example.** Input `INT INT PLUS INT` where `INT PLUS INT` was
expected (extra `INT` at position 1):

```
    node 0       node 1       node 2       SINK
      │            │            │            │
      ├─skip(0.5)─►│            │            │
      ├─del(1.0)──►│            │            │
      ├─sub(1.5)──►│            │            │
      ├─ins(2.0)───┼────────────┼────────────►
      ├─swap(1.25)─┼────────────►            │
      │            ├─skip(0.5)─►│            │
      │            │            ├─sync(0.0)──►
      │            ├─sync(0.0)──┼────────────►

    Viterbi: node 0 →[skip, 0.5]→ node 1 →[sync, 0.0]→ SINK
    Total cost: 0.5 (skip the extra INT, sync at PLUS)
```

**Source**: `recovery.rs:128–228`

#### 6.2.2 Edit Distance Counting (B2)

**Semiring**: EditWeight

**Discrete cost table**:

| Operation  | Edit Count | Rationale                                                 |
|------------|:----------:|-----------------------------------------------------------|
| Skip       |     1      | Consume one unexpected token                              |
| Delete     |     1      | Remove one token                                          |
| Insert     |     2      | Fabricate a token (asymmetric: fabrication > consumption) |
| Substitute |     2      | Replace one token (equivalent to delete + insert)         |

**Rationale.** The edit count is an integer-valued metric tracking the *number*
of editing operations, independent of their tropical cost. The asymmetry
between consumption (1) and fabrication (2) reflects the principle that
fabricating tokens from nothing is structurally more invasive than consuming
or removing existing tokens. Edit counts compose under `⊗  = +` (accumulate
along a path).

**Example.** A repair sequence "skip 2 tokens + insert 1 token":

```
    edit_total = skip(1) + skip(1) + insert(2) = EditWeight(4)
```

**Source**: `semiring.rs:405–425`

#### 6.2.3 Dual-Cost Recovery (B3)

**Semiring**: ProductWeight\<TropicalWeight, EditWeight\>

**Formula**:

> RecoveryCost = (w_tropical, n_edits)

The recovery Viterbi operates over `ProductWeight<TropicalWeight, EditWeight>`,
jointly tracking tropical cost (for optimality) and edit count (for
diagnostics). The lexicographic ordering of `ProductWeight` ensures:

1. **Primary**: Minimize tropical cost (continuous, fine-grained)
2. **Tiebreak**: Minimize edit count (discrete, for human readability)

**Example.** Two repair paths reaching the same sync point:

```
    Path A: (1.5, 3)  — cost 1.5, 3 edits
    Path B: (1.5, 2)  — cost 1.5, 2 edits
    ─────────────────────────────────────────
    Lexicographic comparison: same tropical → fewer edits wins
    Winner: Path B
```

**Source**: `recovery.rs` (type alias `RecoveryCost`)

#### 6.2.4 Identity Assignment (B4)

**Semiring**: any `W: Semiring`

**Formula**:

> ∀ token tᵢ : w(tᵢ) = W::one()

When converting a linear (unambiguous) token stream to a generic lattice via
`linear_to_lattice_generic<W>()`, every edge receives the semiring
multiplicative identity `W::one()`. For TropicalWeight, `one() = 0.0`; for
CountingWeight, `one() = 1`; for BooleanWeight, `one() = true`.

**Rationale.** Unambiguous linear streams have no weight differentiation —
all tokens are equally valid. The multiplicative identity preserves under
composition: for any weight `w`, `w ⊗  one() = w`. This ensures that injecting
a linear stream into a generic lattice framework does not distort weights
computed by upstream or downstream methods.

**Source**: `lattice.rs:568–576`

#### 6.2.5 Position Weight Penalty (B5)

**Semiring**: TropicalWeight

**Formula**:

> w_adjusted = w_original + |Δpos| × 0.5
>
> where Δpos = alt_pos − primary_pos (token positions consumed)

When an NFA alternative parse consumed a different number of tokens than the
primary parse, its weight is adjusted by a position-proportional penalty. This
implements a "longest match" preference analogous to maximal-munch lexing.

**Rationale.** Alternatives that consume more input are generally preferable
(they explain more of the token stream). Alternatives that consume less input
leave unconsumed tokens that may cause downstream parse failures. The symmetric
penalty `|Δpos| × 0.5` ensures that a shorter match must have a proportionally
lower raw weight to remain competitive against the primary interpretation.

**Example.** Primary parse consumed to position 13 (13 tokens). An alternative
consumed to position 11:

```
    Δpos = |11 − 13| = 2
    penalty = 2 × 0.5 = 1.0
    w_adjusted = w_original + 1.0
```

If the alternative's raw weight was 0.3 and the primary's weight was 0.4, the
adjusted weight becomes 1.3 — the primary (0.4) now wins despite having higher
raw weight.

**Constant**: `POSITION_WEIGHT_PENALTY = 0.5`

**Source**: `wfst.rs:1124`

---

### 6.3 Training Methods (wfst-log gated)

#### 6.3.1 Probabilistic Weights (C1)

**Semiring**: LogWeight

**Feature gate**: `wfst-log`

**Formula**:

> w = −ln(p), where p ∈ (0, 1] is the estimated probability.

The log semiring represents probabilities in negative-log space. Lower weight
= higher probability. The semiring operations are:

| Operation  | Formula                | Probability-Space Equivalent |
|------------|------------------------|------------------------------|
| ⊕  (plus)  | −ln(exp(−a) + exp(−b)) | p_a + p_b (sum)              |
| ⊗  (times) | a + b                  | p_a × p_b (product)          |
| zero       | +∞                     | 0 (impossible)               |
| one        | 0.0                    | 1 (certain)                  |

**Conversion**:
- Probability → weight: `w = −ln(p)`
- Weight → probability: `p = exp(−w)`

**SGD update.** During training, weights are updated by stochastic gradient
descent on the log-likelihood:

> w ← w − η(expected_correct − expected_all)

where `expected_correct` and `expected_all` are computed via forward-backward
over the training corpus. Weight corrections recorded in `WEIGHT_CORRECTIONS`
during parsing provide the gradient signal.

**Source**: `semiring.rs:936–939`

#### 6.3.2 Entropy / Information Content (C2)

**Semiring**: EntropyWeight

**Feature gate**: `wfst-log`

**Formula**:

> (w, e) = (−ln(p), −ln(p))

For Shannon entropy computation, the expectation component is set equal to the
weight for each arc. After forward-backward propagation, the final expectation
gives the entropy H of the parse distribution:

> H = −Σᵢ pᵢ ln(pᵢ) (in nats)

Divide by `ln(2)` to convert to bits.

The EntropyWeight semiring composes as:

| Operation  | Weight Component           | Expectation Component                                     |
|------------|----------------------------|-----------------------------------------------------------|
| ⊕  (plus)  | −ln(exp(−w_a) + exp(−w_b)) | (e_a·exp(−w_a) + e_b·exp(−w_b)) / (exp(−w_a) + exp(−w_b)) |
| ⊗  (times) | w_a + w_b                  | e_a + e_b                                                 |

**Application**: High entropy → widen beam width (many plausible alternatives);
low entropy → narrow beam (single dominant alternative). This drives the
adaptive beam thresholds `ENTROPY_BEAM_LOW_THRESHOLD = 0.5` and
`ENTROPY_BEAM_MAX = 10.0`.

**Source**: `semiring.rs:1141`

---

### 6.4 Weight Flow Summary

The following diagram traces how weights flow between the three lifecycle
phases. Compile-time weights (A1–A4) are baked into generated match arms;
runtime methods (B1–B5) operate over those baked-in values; training methods
(C1–C2) can update the compile-time weights via the feedback loop.

```
    ┌──────────────────── Compile Time ─────────────────────┐
    │                                                       │
    │  A1 (priority) ─► DFA accept_weight()                 │
    │  A2 (action)  ─┐                                      │
    │  A3 (specific) ┴► A4 (compose) ─► AMBIGUOUS_WEIGHTS   │
    │  A5 (count)   ─► ambiguity diagnostics (W05)          │
    │  A6 (reach)   ─► dead-rule diagnostics                │
    │  A7 (context) ─► grammar overlap analysis             │
    │  A8 (complex) ─► bottleneck diagnostics               │
    │  A9 (nbest)   ─► confidence_gap diagnostics           │
    │                       │                               │
    └───────────────────────┊───────────────────────────────┘
                            │ baked into generated code
    ┌───────────────────────┊───────────────────────────────┐
    │                       ▼         Runtime               │
    │                                                       │
    │  B1 (repair costs) ──► viterbi_multi_step()           │
    │  B2 (edit counts)  ──► RecoveryCost right component   │
    │  B3 (dual-cost)    ──► lexicographic Viterbi          │
    │  B4 (identity)     ──► linear_to_lattice_generic()    │
    │  B5 (position)     ──► NFA replay weight adjustment   │
    │                                                       │
    │  WEIGHT_CORRECTIONS ◄── from_alternatives() feedback  │
    │         │                                             │
    └─────────┊─────────────────────────────────────────────┘
              │ drain after parsing
    ┌─────────┊─────────────────────────────────────────────┐
    │         ▼       Training (wfst-log)                   │
    │                                                       │
    │  C1 (log prob) ──► SGD weight update                  │
    │  C2 (entropy)  ──► adaptive beam width                │
    │         │                                             │
    │         └──► updated weights ──► re-pipeline          │
    └───────────────────────────────────────────────────────┘
```

---

## 7. Worked Example: End-to-End

Trace the input `float(1 == 1)` through the RhoCalc grammar, which has both
a `float()` cast rule and function-call syntax.

### Step 1: Lexing (Conversion Point ②)

`lex_weighted_core()` produces a flat weighted stream:

```
Token           Range        Weight
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

### Interlude: Dispatch Weight Origin

Step 1 showed all lex weights at 0.0 — the input is lexically unambiguous.
But Step 3 (below) introduces non-zero **dispatch weights** from compile-time
methods A2–A4. For the full weight assignment formulae and rationale, see
[§6.1 Compile-Time Methods](#61-compile-time-methods-pipeline) — specifically
A2 (action type), A3 (rule specificity), and A4 (composition). The computed
values for this example are:

| Alt  | Rule                          | w_action (A2) | w_specificity (A3) | w_final (A4) |
|------|-------------------------------|:-------------:|:------------------:|:------------:|
| Alt₁ | `FloatCast: float( Expr )`    |      0.0      |        0.40        |   **0.40**   |
| Alt₂ | `FunctionCall: Ident( Args )` |      0.5      |       ≈ 0.36       |  **≈ 0.86**  |

### Step 3: Parsing with NFA Ambiguity

The parser encounters `float` at the dispatch point for category `Expr`. Two
NFA alternatives exist:

| Alt  | Rule                          | Structure       | w_specificity     | w_action                 | w_final    |
|------|-------------------------------|-----------------|-------------------|--------------------------|------------|
| Alt₁ | `FloatCast: float( Expr )`    | 1 term + 1 NT   | 1/(1+1.5) = 0.40  | 0.0 (Direct)             | **0.40**   |
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
                    ╭── FloatCast(EqExpr(1,1))     w=0.40  accepting ──╮
  parse point ──────┤                                                  ├── result
                    ╰── FunctionCall(float,[...])  w≈0.86  accepting ──╯
```

Both are accepting. Stage 2 tiebreaks on WFST weight:

```
argmin_weight(accepting_alternatives):
  Alt₁ (FloatCast):     w = 0.40
  Alt₂ (FunctionCall):  w ≈ 0.86
  ⊕  = min(0.40, 0.86) = 0.40 → Alt₁ wins
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

## 8. Relationship to Semiring Composition

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

### How the Modes Map to Weight Assignment Methods

Each of the 14 weight assignment methods from [§6](#6-weight-assignment-methods)
participates in one or more semiring composition modes:

| Mode | Weight Methods     | Composition Pattern                                           |
|------|--------------------|---------------------------------------------------------------|
| 1    | A1, B4, C1, C2     | Single-semiring operations (priority, identity, log, entropy) |
| 2    | B1, B2, B3         | ProductWeight joint tracking (tropical + edit)                |
| 3    | A2, A3, A4, B5     | Cross-structure flow (pipeline → runtime disambiguation)      |
| —    | A5, A6, A7, A8, A9 | Diagnostic-only (not consumed by lattice structures)          |

---

## 9. See Also

### Weight Assignment Methods

- [§6 Weight Assignment Methods](#6-weight-assignment-methods): All 14 methods
  with formulae, rationale, examples, and diagrams
- [Weight Assignment Method Catalog — Architecture](../../architecture/wfst/stream-to-lattice.md#10-weight-assignment-method-catalog):
  Code-path walkthrough with source-line references for all 14 methods

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
