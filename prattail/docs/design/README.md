# PraTTaIL: Design Rationale

**Date:** 2026-03-04
**Version:** 1.0

## Abstract

PraTTaIL (Pratt-based parser generator for MeTTaIL) is a compile-time parser
generator that unifies Pratt parsing, recursive descent, and Weighted
Finite-State Transducer (WFST) theory into a single framework for
expression-heavy, multi-category languages. This document introduces the major
design component, argues why each was chosen, and explains how they integrate —
with particular emphasis on the non-traditional application of WFST theory to
parser generation.

```
                           ┌─────────────────────────────────────┐
  "Why does PraTTaIL       │  §1  Introduction                   │
   exist?"            ──── │  §2  Pratt Parsing                  │
                           │  §3  Trampoline Architecture        │
  "How does it handle      │  §4  NFA Disambiguation             │
   ambiguity?"        ──── │  §5  WFSTs for Parser Dispatch  ◀── │── Centerpiece
                           │  §6  Semirings                      │
  "What analyses does      │  §7  Token Lattices & Viterbi       │
   it perform?"       ──── │  §8  Error Recovery via WFST        │
                           │  §9  Optimization Cascade           │
  "How does it all         │ §10  Dead-Rule Detection & Linting  │
   fit together?"     ──── │ §11  Integration                    │
                           │ §12  Worked Example                 │
                           │ §13  Conclusion                     │
                           │ §14  References                     │
                           └─────────────────────────────────────┘
```

---

## Table of Contents

- [§1 Introduction — Why PraTTaIL Exists](#1-introduction--why-prattail-exists)
- [§2 Pratt Parsing as the Core Algorithm](#2-pratt-parsing-as-the-core-algorithm)
- [§3 Trampoline Architecture for Stack Safety](#3-trampoline-architecture-for-stack-safety)
- [§4 NFA Disambiguation](#4-nfa-disambiguation)
- [§5 WFSTs for Parser Dispatch](#5-wfsts-for-parser-dispatch) ← Centerpiece
- [§6 Semirings — Parameterized Analysis](#6-semirings--parameterized-analysis)
- [§7 Token Lattices and Viterbi Decoding](#7-token-lattices-and-viterbi-decoding)
- [§8 Error Recovery via WFST](#8-error-recovery-via-wfst)
- [§9 Optimization Cascade](#9-optimization-cascade)
- [§10 Dead-Rule Detection and Linting](#10-dead-rule-detection-and-linting)
- [§11 Integration — How It All Fits Together](#11-integration--how-it-all-fits-together)
- [§12 A Complete Worked Example](#12-a-complete-worked-example)
- [§13 Conclusion and Design Principles](#13-conclusion-and-design-principles)
- [§14 References and Cross-References](#14-references-and-cross-references)

---

## §1 Introduction — Why PraTTaIL Exists

### The Problem

Expression-heavy languages with multiple syntactic categories — such as Rholang,
MeTTa, and lambda calculi — pose a challenge that traditional parser generators
handle poorly:

1. **Ambiguous dispatch.** When the parser sees token `Ident` in category `Expr`,
   should it parse a variable reference, a function application, a pattern match,
   or a channel lookup? LALR resolves this via shift/reduce declarations (fragile),
   PEG via ordered choice (silent priority bugs).

2. **Cross-category expressions.** An `Int` expression may appear inside a `Bool`
   comparison (`3 > 2`), which may appear inside a `Process` (`if (3 > 2) { ... }`).
   Each category boundary requires dispatch decisions that compound ambiguity.

3. **Error recovery.** When the input is malformed, the parser must decide how to
   repair it. Traditional panic-mode recovery skips tokens until a synchronization
   point — a heuristic with no optimality guarantees.

### The Thesis

**WFST theory provides a unified algebraic framework** for dispatch, recovery,
disambiguation, linting, and optimization — all derived from a single data
structure built at compile time. The same WFST, evaluated under different
semirings, answers different questions:

| Semiring          | Question Answered                              |
|-------------------|------------------------------------------------|
| TropicalWeight    | What is the best dispatch path?                |
| BooleanWeight     | Is this rule reachable?                        |
| CountingWeight    | How many derivations exist? (ambiguity degree) |
| EditWeight        | What is the minimum-cost repair?               |
| LogWeight         | What is the partition function? (training)     |

This is not a natural fit that anyone would stumble upon — WFSTs originate in
speech recognition (Mohri et al., 2002) and computational linguistics, not in
parser generation. §5 develops this argument in detail.

### Performance

PraTTaIL generates Rust code that is **21–900× faster** than equivalent LALRPOP
parsers, with a geometric mean speedup of approximately **192×** across benchmark
grammars. All WFST computation occurs at compile time; the generated parser
carries only static weight arrays and match-arm orderings.

> **Cross-references:**
> [design/motivation.md](motivation.md) ·
> [theory/parsing-landscape.md](../theory/parsing-landscape.md)

---

## §2 Pratt Parsing as the Core Algorithm

### Why Pratt Parsing?

Vaughan Pratt's top-down operator-precedence algorithm (Pratt, 1973) is
**operator-centric, not grammar-centric**. Instead of encoding precedence via
layers of grammar productions (as in LALR) or ordered alternatives (as in PEG),
Pratt assigns a *binding power pair* `(left_bp, right_bp)` to each operator and
resolves precedence via numeric comparison at parse time.

| Approach          | Precedence Encoding         | Ambiguity Handling        |
|-------------------|-----------------------------|---------------------------|
| LALR              | Tiered grammar productions  | Shift/reduce declarations |
| PEG               | Ordered alternatives        | First-match wins silently |
| **Pratt**         | **Binding power numbers**   | **Numeric comparison**    |

This has two key advantages:

1. **Adding an operator is O(1).** Declare its binding powers; no grammar
   restructuring needed.
2. **Associativity falls out of the asymmetry.** Left-associative operators use
   `(bp, bp+1)`, right-associative use `(bp+1, bp)`.

### Binding Power Assignment

PraTTaIL assigns binding powers in a two-pass analysis:

```
Pass 1: Non-postfix operators (declaration order, lowest precedence first)
  Starting bp = 2   (0 reserved for entry, 1 as sentinel)
  Left-assoc:  (bp, bp+1),  bp += 2
  Right-assoc: (bp+1, bp),  bp += 2

Pass 2: Postfix operators (above non-postfix range)
  Unary prefix:  bp = max_non_postfix_bp + 2
  Postfix:       bp = max_non_postfix_bp + 4+
```

### The Pratt Loop

The core algorithm is a tight loop that alternates between *null denotation*
(prefix/atom parsing) and *left denotation* (infix/postfix continuation):

```
fn parse(tokens, pos, min_bp) → Result<AST, Error>:
    // NUD: parse prefix or atom
    lhs ← dispatch_nud(tokens, pos)

    // LED: consume infix/postfix while binding power permits
    loop:
        op ← peek(tokens, pos)
        (left_bp, right_bp) ← bp_table[op]  or break
        if left_bp < min_bp:
            break
        advance(pos)
        rhs ← parse(tokens, pos, right_bp)   // recursive call
        lhs ← make_infix(op, lhs, rhs)

    return lhs
```

### Parse Trace: `1 + 2 * 3`

Assume `+` has `(2, 3)` and `*` has `(4, 5)`:

```
parse(min_bp=0)
  ├─ NUD: lhs = Int(1)
  ├─ LED: op=+, left_bp=2 ≥ 0 ✓
  │   ├─ parse(min_bp=3)
  │   │   ├─ NUD: lhs = Int(2)
  │   │   ├─ LED: op=*, left_bp=4 ≥ 3 ✓
  │   │   │   ├─ parse(min_bp=5)
  │   │   │   │   ├─ NUD: lhs = Int(3)
  │   │   │   │   └─ LED: end of input → return Int(3)
  │   │   │   └─ lhs = Mul(Int(2), Int(3))
  │   │   └─ LED: end of input → return Mul(Int(2), Int(3))
  │   └─ lhs = Add(Int(1), Mul(Int(2), Int(3)))
  └─ return Add(Int(1), Mul(Int(2), Int(3)))

Result: 1 + (2 * 3)  ✓
```

The binding power comparison `left_bp=4 ≥ 3` at `*` causes it to bind tighter
than `+`, producing the correct parse tree without any grammar layering.

### In PraTTaIL

PraTTaIL generates the Pratt loop at compile time via `write_pratt_parser()` in
`pratt.rs`. Binding powers are computed by `analyze_binding_powers()` and emitted
as constant lookup tables. The NUD dispatch (which rule to try for a given prefix
token) is where WFSTs enter the picture — see §5.

> **Cross-references:**
> [design/pratt-generator.md](pratt-generator.md) ·
> [theory/pratt-parsing.md](../theory/pratt-parsing.md)

---

## §3 Trampoline Architecture for Stack Safety

### The Problem

The Pratt loop's recursive call `rhs ← parse(tokens, pos, right_bp)` uses the OS
call stack. For deeply nested expressions — common in Rholang process algebra and
lambda calculi — this crashes at approximately **10,000 nesting depth** due to
stack overflow.

### The Solution: Explicit Continuation Stack

PraTTaIL replaces recursion with an explicit `Vec<Frame_Cat>` continuation stack
allocated on the heap, managed via thread-local pooling:

```
                 Recursive Descent              Trampoline
              ┌─────────────────────┐   ┌────────────────────────┐
              │  OS Stack (~8MB)    │   │  Heap (growable)       │
              │  ┌──────────────┐   │   │  ┌──────────────────┐  │
  depth=10000 │  │ parse frame  │   │   │  │ Vec<Frame_Cat>   │  │
              │  │ parse frame  │   │   │  │ ┌──────────────┐ │  │
              │  │ parse frame  │   │ ╳ │  │ │ InfixRHS     │ │  │
              │  │     ⋮        │   │   │  │ │ GroupClose   │ │  │
              │  │ parse frame  │ ← │   │  │ │ UnaryPrefix  │ │  │
              │  └──────────────┘   │   │  │ │     ⋮        │ │  │
              │  ⚠ STACK OVERFLOW   │   │  │ │ InfixRHS     │ │  │
              └─────────────────────┘   │  │ └──────────────┘ │  │
                                        │  └──────────────────┘  │
                                        │  ✓ 100K+ depth         │
                                        └────────────────────────┘
```

### Frame Variants

Each grammar category gets a generated `Frame_<Cat>` enum with variants for every
continuation point:

| Variant                      | Purpose                                    |
|------------------------------|--------------------------------------------|
| `InfixRHS { lhs, op_pos }`   | Awaiting right operand of infix operator   |
| `GroupClose { saved_bp }`    | Awaiting `)` to close parenthesized group  |
| `UnaryPrefix_X { saved_bp }` | Awaiting operand of unary prefix `X`       |
| `RuleLabel_SegN { … }`       | Multi-nonterminal RD handler, at segment N |
| `CollectionElem_X { … }`     | Collecting elements of a list/set/map      |
| `Mixfix_X_i { lhs, … }`      | Ternary/mixfix at operand position i       |
| `LambdaBody_Single { … }`    | After binder, awaiting lambda body         |

All frame types are `'static` (no lifetimes — all owned data) to enable
thread-local pooling via `Cell<Vec<Frame_Cat>>`.

### Trampoline Loop Pseudocode

```
fn parse_Cat_own(tokens, pos, min_bp) → Result<Cat, ParseError>:
    frames ← FRAME_POOL_CAT.take()     // reuse allocation
    frames.clear()

    'drive: loop
        // ── NUD Phase ──
        if FORCED_PREFIX is Some(result):
            lhs ← result               // NFA replay override
        else:
            lhs ← dispatch_nud(tokens, pos)  // WFST-ordered arms

        // ── LED Phase ──
        'led: loop
            op ← peek(tokens, pos)
            if has_infix_bp(op):
                (left_bp, right_bp) ← infix_bp(op)
                if left_bp < min_bp: break 'led
                advance(pos)
                frames.push(InfixRHS { lhs, op_pos, saved_bp: right_bp })
                min_bp ← right_bp
                continue 'drive        // ← replaces recursive call

            if frames.is_empty(): break 'drive

            // Unwind: pop frame, apply continuation
            match frames.pop():
                InfixRHS { lhs: prev_lhs, op_pos, .. } →
                    lhs ← make_infix(op_pos, prev_lhs, lhs)
                GroupClose { saved_bp } →
                    expect(tokens, pos, RParen)
                    min_bp ← saved_bp
                // ... other frame variants ...

    FRAME_POOL_CAT.set(frames)          // return allocation to pool
    Ok(lhs)
```

### Performance

| Metric            | Recursive Descent | Trampoline | Δ        |
|-------------------|-------------------|------------|----------|
| Max nesting depth | ~10,000           | 100,000+   | **10×+** |
| Nesting benchmark | baseline          | −15%       | faster   |
| Infix benchmark   | baseline          | −9%        | faster   |
| Flat expressions  | baseline          | ≈0%        | no cost  |

The improvement for non-nested expressions comes from frame pool reuse
eliminating per-parse allocation overhead.

> **Cross-references:**
> [design/lazy-trampoline-parser.md](lazy-trampoline-parser.md) ·
> Source: `prattail/src/trampoline.rs`

---

## §4 NFA Disambiguation

### The Problem

When the parser encounters token `Ident` in category `Expr`, multiple rules may
claim it as their dispatch token:

```
  Token: Ident
    ├─── POutput:  output!(name, data)    weight: 1.2
    ├─── PLookup:  name.field             weight: 2.0
    ├─── PVar:     name                   weight: 0.5  ← cheapest
    └─── PApply:   name(arg1, arg2)       weight: 1.8
```

Which rule should the parser try first?

### Four-Layer Resolution Hierarchy

PraTTaIL resolves dispatch ambiguity through a hierarchy of increasingly
powerful strategies:

```
  ┌────────────────────────────────────────────────────────────────┐
  │ Layer 1: Two-Token Lookahead                                   │
  │   peek(pos+1) resolves: Ident + LParen → PApply                │
  │                          Ident + Dot   → PLookup               │
  │                          Ident + Bang  → POutput               │
  ├────────────────────────────────────────────────────────────────┤
  │ Layer 2: Left-Factored Prefix Walking                          │
  │   shared prefix consumed once, branch at divergence point      │
  ├────────────────────────────────────────────────────────────────┤
  │ Layer 3: NFA Merged Prefix                                     │
  │   try all matching rules simultaneously, collect results       │
  │   to spillover buffer: Vec<(Cat, usize, f64)>                  │
  ├────────────────────────────────────────────────────────────────┤
  │ Layer 4: WFST Weight Ordering                                  │
  │   try cheapest alternative first (tropical weight)             │
  │   demand-driven replay with weight-threshold pruning           │
  │   REPLAY_WEIGHT_SLACK = 2.0 tropical units                     │
  └────────────────────────────────────────────────────────────────┘
```

**Layer 4** is the key innovation: by ordering alternatives by their WFST weight
(lowest = most likely), the parser tries the statistically cheapest parse first.
The spillover buffer is sorted ascending by weight at the push site, and the
acceptance drain loop **short-circuits on the first accepting replay** — so in the
common case, only one alternative is tried.

### Weight-Threshold Pruning

```
primary_weight ← weight of the first (cheapest) alternative
REPLAY_WEIGHT_SLACK ← 2.0

for (alt, pos, weight) in spillover_buffer:
    if weight > primary_weight + REPLAY_WEIGHT_SLACK:
        break       // remaining alternatives too expensive
    result ← replay(alt, pos)
    if result.is_accepting():
        return result   // short-circuit
```

This is a **beam search** over parse alternatives, with the beam width determined
by the WFST's tropical weights rather than by an arbitrary threshold.

### Dispatch-Aware NFA Fallback

When NFA merged-prefix replay detects a cross-category inner expression (e.g.,
`bool(1 == 1)` — a cast rule where the inner `1 == 1` is an `Int` comparison
inside a `Bool` context), the fallback calls `parse_Cat()` directly instead of
pushing a continuation frame, ensuring dispatch-aware parsing of the inner
expression.

> **Cross-references:**
> [design/disambiguation/08-nfa-wfst-disambiguation.md](disambiguation/08-nfa-wfst-disambiguation.md) ·
> [architecture/wfst/nfa-spillover-architecture.md](../architecture/wfst/nfa-spillover-architecture.md)

---

## §5 WFSTs for Parser Dispatch

*This section is the centerpiece of the document. It argues that Weighted
Finite-State Transducers — a tool from speech recognition and computational
linguistics — are an excellent and non-traditional fit for parser generation.*

### §5.1 What Is a WFST?

A **Weighted Finite-State Transducer** is a finite automaton whose transitions
carry weights from an algebraic structure called a *semiring*. Formally:

> **Definition.** A WFST over semiring 𝕊 = (𝕂, ⊕, ⊗, 0̄, 1̄) is a tuple
> M = (Σ, Q, I, F, δ, λ, ρ) where:
> - Σ is the input alphabet
> - Q is a finite set of states
> - I ⊆ Q is the set of initial states
> - F ⊆ Q is the set of final states
> - δ ⊆ Q × (Σ ∪ {ε}) × Q × 𝕂 is the set of weighted transitions
> - λ : I → 𝕂 assigns initial weights
> - ρ : F → 𝕂 assigns final weights

The **weight of a path** π = (q₀, a₁, q₁, w₁) · … · (qₙ₋₁, aₙ, qₙ, wₙ) is:

```
w(π) = λ(q₀) ⊗  w₁ ⊗  … ⊗  wₙ ⊗  ρ(qₙ)
```

The **weight of a string** x is the ⊕-sum over all accepting paths:

```
‖M‖(x) = ⊕ _{π accepts x} w(π)
```

In the **tropical semiring** (ℝ⁺ ∪ {+∞}, min, +, +∞, 0), this reduces to
finding the *minimum-cost path* — exactly the shortest-path problem.

**A 3-node dispatch WFST:**

```
                    Ident / PVar / 0.5
        ┌───────────────────────────────────┐
        │                                   ▼
  ┌─────┴─────┐   Ident / POutput / 1.2   ┌──────┐
  │   q₀      │──────────────────────────▶│  q₁  │
  │  (start)  │   Ident / PLookup / 2.0   │      │
  │  λ = 0.0  │──────────────────────────▶│ρ=0.0 │
  └───────────┘   Ident / PApply / 1.8    └──────┘
        │──────────────────────────────────▶   ▲
        └──────────────────────────────────────┘
```

All four rules dispatch on `Ident`, but with different weights. The shortest path
(weight 0.5) selects `PVar` — the most common interpretation.

### §5.2 The Key Insight: Parser Dispatch IS a Weighted Decision Problem

Here is the central argument of this document:

> **Thesis.** Given a token `t` at position `p` in category `C`, choosing which
> parse rule to try first is a **shortest-path query** on a weighted graph — and
> this is exactly what WFSTs are designed to compute.

The mapping is direct:

| WFST Component  | Parser Interpretation                            |
|-----------------|--------------------------------------------------|
| Σ (alphabet)    | Token variants (`Ident`, `LParen`, `Int`, …)     |
| Q (states)      | Parse contexts (category × disambiguation stage) |
| δ (transitions) | Dispatch decisions (which rule to invoke)        |
| 𝕂 (weights)     | Priority/cost of each dispatch choice            |
| ⊕  (plus)       | Combine alternative paths (`min` for tropical)   |
| ⊗  (times)      | Sequence path segments (`+` for tropical)        |

**Why this matters.** Traditional parser generators treat dispatch as a
*table lookup* (LALR action table) or *ordered list* (PEG). Both are first-order:
they cannot express that "rule A is 3× more likely than rule B when preceded by
token X". WFSTs make dispatch a *weighted optimization problem*, enabling:

1. **Optimal ordering** — the cheapest (most likely) rule is tried first
2. **Confidence scoring** — the gap between best and second-best quantifies
   ambiguity
3. **Graceful degradation** — if the best rule fails, alternatives are tried in
   weight order, not arbitrary order

**Concrete example: Calculator's `Int` category.**

```
                 IntLit / ParseInt / 0.0
  ┌─────────┐ ─────────────────────────────▶  ┌─────────┐
  │  start  │    LParen / GroupExpr / 0.5     │  accept │
  │ λ = 0.0 │ ─────────────────────────────▶  │ ρ = 0.0 │
  └─────────┘    Minus / Negate / 1.0         └─────────┘
        │     ─────────────────────────────▶      ▲
        └─────────────────────────────────────────┘
```

When the parser sees `IntLit`, it unambiguously dispatches to `ParseInt`
(weight 0.0). When it sees `LParen`, it dispatches to `GroupExpr` (weight 0.5).
When it sees `Minus`, it dispatches to `Negate` (weight 1.0). The ordering is
*algebraically determined*, not declared by the grammar author.

### §5.3 Unification: One Representation, Six Uses

The deepest advantage of WFSTs is that the **same data structure**, evaluated
under **different semirings**, answers **different questions**:

```
                    ┌──────────────┐
                    │              │
  TropicalWeight ──▶│              │──▶ Best dispatch path
  BooleanWeight  ──▶│  Same WFST   │──▶ Reachability (dead rules)
  CountingWeight ──▶│    M = …     │──▶ Ambiguity degree
  EditWeight     ──▶│              │──▶ Minimum-cost repair
  LogWeight      ──▶│              │──▶ Partition function (training)
                    │              │
                    └──────────────┘
```

| Concern            | Traditional Parser Generator  | PraTTaIL (WFST)                        |
|--------------------|-------------------------------|----------------------------------------|
| **Dispatch**       | Action table / ordered choice | Shortest-path query (TropicalWeight)   |
| **Dead rules**     | Manual inspection             | BooleanWeight reachability analysis    |
| **Ambiguity**      | Shift/reduce conflict report  | CountingWeight derivation counting     |
| **Error recovery** | Panic-mode heuristic          | EditWeight minimum-cost repair         |
| **Optimization**   | Per-concern ad-hoc passes     | TransducerCascade (weight-preserving)  |
| **Composition**    | Grammar union (conflicts)     | Weighted union with weight arbitration |

The key formula is:

> **Same algorithm + different semiring = different analysis.**

```rust
// Dispatch: which rule to try first?
let best = forward::<TropicalWeight>(&wfst, token);      // min-cost path

// Dead rules: is this rule reachable at all?
let alive = forward::<BooleanWeight>(&wfst, token);       // ∃ accepting path?

// Ambiguity: how many ways can this token be parsed?
let count = forward::<CountingWeight>(&wfst, token);      // Σ derivations

// Recovery: what is the cheapest way to fix this error?
let repair = forward::<EditWeight>(&wfst, token);         // min-edit path

// Training: what is the total probability mass?
let Z = forward::<LogWeight>(&wfst, token);               // log-sum-exp
```

This is not merely elegant — it is **economical**. Building one WFST per category
at compile time amortizes the cost of constructing the dispatch graph across all
downstream analyses. No separate data structures are needed for dead-rule
detection, ambiguity analysis, or recovery planning.

### §5.4 Algebraic Guarantees vs Heuristics

Traditional conflict resolution is **ad-hoc**:

- LALR: shift/reduce conflicts resolved by declaration order or `%left`/`%right`
  annotations — the grammar author manually breaks ties
- PEG: ordered choice (`/`) silently selects the first matching alternative — the
  grammar's textual order determines semantics
- GLR: maintains all alternatives (expensive) and relies on the user to prune

WFSTs provide **algebraic guarantees** via the semiring axioms:

| Axiom                     | Consequence for Dispatch                  |
|---------------------------|-------------------------------------------|
| Commutativity of ⊕        | Dispatch is independent of rule ordering  |
| Associativity of ⊗        | Multi-step paths evaluate in any grouping |
| Distributivity (⊗  over ⊕) | Prefix factoring preserves optimal paths  |
| Annihilation (0̄ ⊗  a = 0̄)  | Unreachable paths propagate correctly     |

**Commutativity of ⊕** is particularly important: it means that the optimal
dispatch decision does not depend on the order in which rules are written in the
grammar. The same grammar, with rules in any order, produces the same WFST
weights and therefore the same dispatch behavior. This eliminates an entire class
of bugs that plagues PEG parsers, where reordering alternatives silently changes
the parse semantics.

**Distributivity** ensures that when PraTTaIL left-factors shared prefixes (a
standard optimization — see §9), the optimal dispatch path is preserved. In a
PEG parser, rewriting `A / B` where A and B share a prefix into a factored form
can change which alternative matches; with WFSTs, factoring is a
weight-preserving transformation.

### §5.5 Comparison Against Alternatives

| Technique    | Dispatch       | Ambiguity   | Recovery    | Composable | Weighted |
|--------------|----------------|-------------|-------------|------------|----------|
| LALR         | Action table   | Conflicts   | Panic-mode  | ✗          | ✗        |
| LL(k)        | FIRST/FOLLOW   | Conflicts   | FOLLOW sets | ✗          | ✗        |
| PEG          | Ordered choice | Silent      | Manual      | ✗          | ✗        |
| GLR          | All parses     | Fork+merge  | Heuristic   | ~          | ✗        |
| Earley       | Chart          | Complete    | Chart-based | ~          | ✗        |
| **PraTTaIL** | **WFST**       | **Counted** | **Optimal** | **✓**      | **✓**    |

PraTTaIL is the only approach in this table that provides:
- **Weighted dispatch** (optimal rule ordering via tropical shortest path)
- **Quantified ambiguity** (counting semiring gives exact derivation count)
- **Optimal recovery** (edit semiring minimizes repair cost)
- **Algebraic composability** (weighted union preserves correctness)

### §5.6 Why Speech Recognition Theory Applies

The application of WFSTs to parser generation is non-obvious because WFSTs
originate in a different domain. But the **structural analogy** is exact:

```
  Speech Recognition       Parser Generation
  ─────────────────────    ──────────────────────
  Acoustic signal          Character stream
       │                        │
       ▼                        ▼
  Phoneme lattice          Token lattice
       │                        │
       ▼                        ▼
  Word sequence            Parse tree
       │                        │
       ▼                        ▼
  Sentence meaning         AST / semantic value
```

Both face the **same fundamental problem**: an ambiguous input signal must be
decoded into structured output through a sequence of weighted alternatives. The
mathematical machinery — semirings, Viterbi decoding, forward-backward scoring,
transducer composition, beam pruning — transfers directly.

This is not a metaphor. PraTTaIL literally reuses:

- **Viterbi algorithm** for best-path extraction (lattice.rs, recovery.rs)
- **Forward-backward** for partition functions and training (forward_backward.rs)
- **Transducer composition** for grammar union (compose.rs)
- **Beam pruning** for search space control (transducer.rs)
- **N-best extraction** for alternative parse enumeration (lattice.rs)

The speech recognition community has refined these algorithms over 30+ years. By
building on this foundation, PraTTaIL inherits their correctness guarantees,
performance characteristics, and well-understood trade-offs.

> **Cross-references:**
> [theory/wfst/weighted-automata.md](../theory/wfst/weighted-automata.md) ·
> [theory/wfst/semirings.md](../theory/wfst/semirings.md) ·
> [design/composed-dispatch.md](composed-dispatch.md) ·
> [design/wfst/prediction.md](wfst/prediction.md)

---

## §6 Semirings — Parameterized Analysis

### The Semiring Trait

A semiring 𝕊 = (𝕂, ⊕, ⊗, 0̄, 1̄) is an algebraic structure with two operations:

- **⊕  (plus):** combines parallel paths (commutative monoid with identity 0̄)
- **⊗  (times):** sequences path segments (monoid with identity 1̄)
- **Distributivity:** ⊗  distributes over ⊕
- **Annihilation:** 0̄ ⊗  a = a ⊗  0̄ = 0̄

In Rust:

```rust
pub trait Semiring: Clone + Copy + Debug + PartialEq + Send + Sync + 'static {
    fn zero() -> Self;                          // 0̄
    fn one() -> Self;                           // 1̄
    fn plus(&self, other: &Self) -> Self;       // ⊕
    fn times(&self, other: &Self) -> Self;      // ⊗
    fn is_zero(&self) -> bool;
    fn is_one(&self) -> bool;
    fn approx_eq(&self, other: &Self, epsilon: f64) -> bool;
}
```

### Semiring Catalog

PraTTaIL implements 10 semirings, each answering a different question:

| Semiring           | 𝕂             | ⊕           | ⊗           | 0̄     | 1̄       | Question Answered       |
|--------------------|---------------|-------------|-------------|-------|---------|-------------------------|
| `TropicalWeight`   | ℝ⁺ ∪ {+∞}     | min         | +           | +∞    | 0.0     | Best dispatch path      |
| `BooleanWeight`    | {false, true} | ∨           | ∧           | false | true    | Is this rule reachable? |
| `CountingWeight`   | ℕ             | +           | ×           | 0     | 1       | How many derivations?   |
| `EditWeight`       | ℕ ∪ {∞}       | min         | +           | ∞     | 0       | Minimum edit cost       |
| `ContextWeight`    | 𝒫(Labels)     | ∪           | ∩           | ∅     | U       | Follow-set tightening   |
| `ComplexityWeight` | ℕ ∪ {∞}       | min         | max         | ∞     | 0       | Lookahead budget        |
| `ProductWeight`    | S₁ × S₂       | comp. ⊕     | comp. ⊗     | (0̄,0̄) | (1̄,1̄)   | Joint optimization      |
| `LogWeight`†       | ℝ⁺ ∪ {+∞}     | log-sum-exp | +           | +∞    | 0.0     | Partition function      |
| `EntropyWeight`†   | (ℝ⁺, ℝ)       | LSE mixture | add fields  | (∞,0) | (0,0)   | Shannon entropy         |
| `NbestWeight<N>`†  | Sorted[N]     | merge top-N | cross top-N | empty | [(0,0)] | N-best parse tracking   |

†: Gated behind the `wfst-log` feature (training and probabilistic analysis).

### Parameterized Analysis in Practice

The same Viterbi algorithm works with any semiring that implements `Ord`:

```rust
// Best tokenization (tropical = minimum cost)
let best: ViterbiPath<Token, Span> =
    viterbi_generic::<_, _, TropicalWeight>(&lattice, final_node)?;

// Minimum edit-distance recovery
let repair: ViterbiPath<Token, Span, EditWeight> =
    viterbi_generic::<_, _, EditWeight>(&lattice, final_node)?;

// Joint: best parse with minimum edits as tiebreaker
let joint: ViterbiPath<Token, Span, ProductWeight<TropicalWeight, EditWeight>> =
    viterbi_generic(&lattice, final_node)?;
```

**`CountingWeight` caveat.** The counting semiring is not Viterbi-compatible as
a primary weight because its zero element (0) is the smallest value under the
natural ordering. Use it via `ProductWeight<TropicalWeight, CountingWeight>` to
get both the optimal path and its derivation count.

> **Cross-references:**
> [theory/wfst/semirings.md](../theory/wfst/semirings.md) ·
> Per-semiring docs: [boolean](wfst/semirings/boolean-weight.md) ·
> [counting](wfst/semirings/counting-weight.md) ·
> [edit](wfst/semirings/edit-weight.md) ·
> [context](wfst/semirings/context-weight.md) ·
> [complexity](wfst/semirings/complexity-weight.md) ·
> [tropical](wfst/semirings/tropical-weight.md) ·
> [log](wfst/semirings/log-weight.md) ·
> [product](wfst/semirings/product-weight.md) ·
> [entropy](wfst/semirings/entropy-weight.md) ·
> [nbest](wfst/semirings/nbest-weight.md)

---

## §7 Token Lattices and Viterbi Decoding

### The Problem

Most parsers assume that lexing is unambiguous: each position in the input maps
to exactly one token. But in practice, token boundaries can be ambiguous:

- `>>=` — is this `>` `>=` or `>>` `=` or `>>=`?
- `--` in some languages — decrement operator or comment start?

### Token Lattices: A Weighted DAG

A **token lattice** represents all possible tokenizations as a weighted directed
acyclic graph:

```
  Position:  0         1         2         3
             ●─────────●────────●─────────●
             │   >     │   >=   │         │
             │ w=0.0   │  w=0.0 │         │
             │        ╱│╲       │         │
             │  >>   ╱ │ ╲  =   │         │
             │ w=0.5╱  │  ╲w=0.0│         │
             │     ╱   │   ╲    │         │
             ●────●    │    ●───●         │
             │         │        │         │
             │  >>=    │        │         │
             │ w=1.0   │        │         │
             ●─────────┼────────┼─────────●
```

Each path through the lattice represents a valid tokenization. The **Viterbi
algorithm** finds the minimum-weight (highest-priority) path in O(|edges|) time.

### Core Types

```rust
pub struct TokenLattice<T, S, W: Semiring = TropicalWeight> {
    edges: Vec<Vec<LatticeEdge<T, S, W>>>,  // adjacency lists by node
}

pub struct LatticeEdge<T, S, W: Semiring = TropicalWeight> {
    pub token: T,          // token variant
    pub span: S,           // source span
    pub to_node: usize,    // target node in lattice
    pub weight: W,         // edge weight from semiring
}

pub enum TokenSource<T, S> {
    Linear(Vec<(T, S)>),            // unambiguous: zero overhead
    Lattice(TokenLattice<T, S>),    // ambiguous: Viterbi selects best
}
```

### Zero Overhead for Unambiguous Input

The `TokenSource::Linear` variant represents the common case where lexing is
unambiguous. It is a plain `Vec<(Token, Span)>` with no graph overhead. The
lattice representation is only constructed when the lexer detects genuine token
boundary ambiguity.

### GPS Analogy

The Viterbi algorithm is the same algorithm your GPS uses to find the shortest
route: given a graph with weighted edges, find the minimum-cost path from start
to finish. In a token lattice, "cities" are character positions, "roads" are
possible tokens, and "distances" are weights. Viterbi finds the best
tokenization just as Dijkstra's algorithm finds the best route — but exploiting
the DAG structure for O(|edges|) instead of O(|edges| log |nodes|).

### Beam Pruning

For large lattices, beam pruning constrains the search:

```rust
pub fn viterbi_best_path_beam<T: Clone, S: Clone>(
    lattice: &TokenLattice<T, S>,
    final_node: usize,
    beam_width: Option<TropicalWeight>,  // only paths within beam of best
) -> Option<ViterbiPath<T, S>>
```

Paths whose accumulated weight exceeds `best_so_far + beam_width` are pruned,
reducing computation without sacrificing the optimal path (as long as the beam is
wide enough).

> **Cross-references:**
> [theory/wfst/viterbi-and-forward-backward.md](../theory/wfst/viterbi-and-forward-backward.md) ·
> [design/wfst/token-lattices.md](wfst/token-lattices.md) ·
> [architecture/wfst/token-lattices.md](../architecture/wfst/token-lattices.md)

---

## §8 Error Recovery via WFST

### Traditional Recovery: Panic Mode

Traditional error recovery uses **panic mode**: when an unexpected token is
encountered, skip tokens until a synchronization token (`;`, `}`, `)`) is found,
then resume parsing. This is a heuristic with no optimality guarantee — it may
skip too few tokens (cascading errors) or too many (lost valid structure).

### PraTTaIL: Recovery as Weighted Search

PraTTaIL models each repair action as a **weighted transition** in a recovery
WFST. The Viterbi algorithm then finds the **minimum-cost repair sequence**:

```
  Error site: expected Ident, got Plus
  ┌──────────────────────────────────────────────────────────────┐
  │                                                              │
  │  ●──── Skip(+) ──────▶ ●──── Skip(2) ────▶ ●  weight: 1.0    │
  │  │     w=0.5           │     w=0.5                           │
  │  │                     │                                     │
  │  ●── Insert(Ident) ──▶ ●                     weight: 2.0     │
  │  │     w=2.0                                                 │
  │  │                                                           │
  │  ●── Delete(+) ──▶ ●── Parse(2) ──▶ ●        weight: 1.0     │
  │       w=1.0                                                  │
  │                                                              │
  │  Viterbi selects: Skip(+), Skip(2) or Delete(+), Parse(2)    │
  │  Both weight 1.0 — tiebreak by fewer repair steps            │
  └──────────────────────────────────────────────────────────────┘
```

### Repair Actions and Costs

```rust
pub enum RepairAction {
    SkipToSync { skip_count, sync_token },  // skip to synchronization point
    InsertToken { token },                   // insert a phantom token
    DeleteToken,                             // delete the unexpected token
    SubstituteToken { replacement },         // replace with expected token
    SwapTokens { pos_a, pos_b },            // transpose adjacent tokens
    Composite { steps },                     // multi-step repair sequence
    CategorySwitch { from, to },            // switch parsing category
}
```

| Action     | Base Cost | EditWeight                     |
|------------|-----------|--------------------------------|
| Skip       | 0.5/token | `EditWeight::new(n)`           |
| Delete     | 1.0       | `EditWeight::delete()` = 1     |
| Swap       | 1.25      | `EditWeight::new(1)`           |
| Substitute | 1.5       | `EditWeight::substitute()` = 2 |
| Insert     | 2.0       | `EditWeight::insert()` = 2     |

### Three-Tier Context Model

Repair costs are dynamically adjusted based on parse context:

**Tier 1 — Depth scaling:**
- Deep nesting (>1000): skip cost × 0.5 (prefer skipping to recover quickly)
- Shallow depth (<10): skip cost × 2.0 (skipping is expensive when structure matters)

**Tier 1 — Binding power scaling:**
- Low BP (<4): skip cost × 0.75 (at top-level, skipping is less disruptive)

**Tier 1 — Frame-kind multipliers:**
- Collection context: insert cost × 0.5 (inserting a delimiter is cheap)
- Grouping context: insert cost × 0.5 (inserting `)` to close a group)
- Bracket context: insert cost × 0.3 (bracket matching is high-priority)
- Mixfix context: substitute cost × 0.75 (substituting a mixfix separator)

### Joint Optimization

Using `ProductWeight<TropicalWeight, EditWeight>`, recovery can jointly optimize
for both dispatch quality and edit distance:

```rust
// Find repair that minimizes (dispatch_cost, edit_cost) lexicographically
let repair = viterbi_recovery_beam(
    token_ids, pos, sync_tokens, beam_width
)?;
```

> **Cross-references:**
> [design/wfst/error-recovery.md](wfst/error-recovery.md) ·
> [design/wfst/recovery-config.md](wfst/recovery-config.md) ·
> [design/wfst/extended-recovery-strategies.md](wfst/extended-recovery-strategies.md) ·
> [architecture/wfst/recovery-state-propagation.md](../architecture/wfst/recovery-state-propagation.md)

---

## §9 Optimization Cascade

### TransducerCascade: Fixed-Point Optimization

The WFST built during pipeline compilation may contain redundant states,
unnormalized weights, or unreachable transitions. PraTTaIL optimizes WFSTs via a
**transducer cascade** — a chain of optimization passes that iterate to a fixed
point:

```rust
pub trait OptimizationPass: Debug {
    fn name(&self) -> &str;
    fn priority(&self) -> u32;               // lower = runs first
    fn is_applicable(&self, wfst: &PredictionWfst) -> bool;
    fn apply(&self, wfst: &mut PredictionWfst) -> PassResult;
}
```

### The Four Passes

```
  ┌─────────────────────┐     ┌──────────────────────┐
  │ WeightNormalization │     │ DeadStateElimination │
  │   priority: 5       ├────▶│   priority: 10       │
  │   normalize so      │     │   remove states      │
  │   best action = 0   │     │   with no outgoing   │
  └────────┬────────────┘     └───────┬──────────────┘
           │                          │
           ▼                          ▼
  ┌───────────────────┐     ┌────────────────────┐
  │ StateMinimization │     │ BeamPruning        │
  │   priority: 20    │◀────┤   (configurable)   │
  │   Hopcroft-style  │     │   drop transitions │
  │   signature merge │     │   beyond beam      │
  └────────┬──────────┘     └────────────────────┘
           │
           ▼
       Converged?
      ╱          ╲
    Yes           No ──▶ repeat (max 100 iterations)
     │
     ▼
   Done
```

### Fixed-Point Iteration

```rust
pub struct TransducerCascade {
    passes: Vec<Box<dyn OptimizationPass>>,  // sorted by priority
    max_iterations: usize,                   // default: 100
}

impl TransducerCascade {
    pub fn run(&self, wfst: &mut PredictionWfst) -> CascadeResult {
        for _ in 0..self.max_iterations {
            let mut changed = false;
            for pass in &self.passes {
                if pass.is_applicable(wfst) {
                    let result = pass.apply(wfst);
                    changed |= result.changes > 0;
                }
            }
            if !changed { break; }  // fixed point reached
        }
    }
}
```

**Convergence guarantee:** Each pass is monotone-decreasing over state count
(it only removes states or transitions, never adds them). Therefore, the cascade
converges in at most |Q| iterations, where |Q| is the initial number of states.
In practice, convergence occurs in 2–3 iterations.

> **Cross-references:**
> [optimization/README.md](../optimization/README.md) ·
> [architecture/wfst/optimization-pipeline.md](../architecture/wfst/optimization-pipeline.md) ·
> [theory/wfst/optimization-transducer-cascade.md](../theory/wfst/optimization-transducer-cascade.md)

---

## §10 Dead-Rule Detection and Linting

### Four-Tier Dead-Rule Detection

PraTTaIL identifies rules that can never fire through a four-tier analysis that
increases in sophistication:

```
  ┌─────────────────────────────────────────────────────────────────┐
  │ Tier 1: LiteralNoNativeType                                     │
  │   Rule dispatches on a literal token (e.g., IntLit) but its     │
  │   category has no native type for that literal.                 │
  ├─────────────────────────────────────────────────────────────────┤
  │ Tier 2: UnreachableCategory                                     │
  │   The rule's category is not reachable via any FIRST set or     │
  │   cross-category edge. Fixed-point over transitive closure.     │
  ├─────────────────────────────────────────────────────────────────┤
  │ Tier 3: WfstUnreachable                                         │
  │   BooleanWeight analysis on the same WFST built for dispatch:   │
  │   forward<BooleanWeight>(wfst) returns false for this rule.     │
  │   This is the key reuse of the dispatch WFST (see §5.3).        │
  ├─────────────────────────────────────────────────────────────────┤
  │ Tier 4: SemanticLiveness                                        │
  │   Transitive closure over semantic dependency groups            │
  │   (equations, rewrites, logic blocks). A rule that is parsing-  │
  │   dead may be resurrected if it appears in a dependency group   │
  │   with a live label.                                            │
  └─────────────────────────────────────────────────────────────────┘
```

Tier 3 is the key insight: it reuses the **same WFST built for dispatch** (§5)
but evaluates it under `BooleanWeight` instead of `TropicalWeight`. No additional
data structure is needed.

### The Lint Layer

PraTTaIL provides **28 lints** across 6 categories, with Rust-compiler-style
output:

| Category  | Prefix | Focus                | Count |
|-----------|--------|----------------------|-------|
| Grammar   | G      | Structure & syntax   | 11    |
| WFST      | W      | Dispatch weights     | 5     |
| Recovery  | R      | Error repair config  | 5     |
| Cross-cat | C      | Cast rules & overlap | 3     |
| Perf      | P      | Performance warnings | 3     |
| Compose   | X      | Multi-grammar union  | 5     |

**Sample output:**

```
warning[W01]: rule `FloatToStr` in category `Str` is dead (Tier 3: WfstUnreachable)
  --> calculator.mttl:42:5
   |
42 |   FloatToStr: float_lit => str_val
   |   ^^^^^^^^^^ this rule can never match
   |
   = hint: the dispatch WFST has no accepting path for this rule's
           dispatch token in this category. Consider removing it or
           adding a cast path from a category that can produce `float_lit`.
```

> **Cross-references:**
> [design/wfst/dead-rule-detection.md](wfst/dead-rule-detection.md) ·
> [design/lint-layer.md](lint-layer.md)

---

## §11 Integration — How It All Fits Together

### Pipeline State Machine

PraTTaIL's compile-time pipeline has three phases:

```
  ┌──────────────┐     ┌─────────────┐     ┌─────────────┐
  │ EXTRACT      │     │ GENERATE    │     │ FINALIZE    │
  ├──────────────┤     ├─────────────┤     ├─────────────┤
  │ Parse macro  ├────▶│ Build WFSTs ├────▶│ Emit Rust   │
  │ Build specs  │     │ Run cascade │     │ code as     │
  │ Compute BP   │     │ Run lints   │     │ TokenStream │
  │ FIRST/FOLLOW │     │ DCE         │     │             │
  └──────────────┘     └─────────────┘     └─────────────┘
```

### Detailed Integration Diagram

```
LanguageSpec (from macro expansion)
     │
     ├──▶ LexerBundle ──▶ NFA → DFA → Minimized DFA
     │         │              │
     │         │              ├─ IS_ACCEPTING bitmap (u128 or bool[])
     │         │              └─ Multi-accept states for token lattices
     │         │
     │         └──▶ write_lexer_code()
     │                  │
     │                  └──▶ lex_core() / lex_weighted_core()
     │
     ├──▶ ParserBundle
     │         │
     │         ├──▶ compute_first_sets()  ──────┐
     │         │    compute_follow_sets()  ──────┤
     │         │                                 │
     │         ├──▶ compute_composed_dispatch()  │
     │         │         │                       │
     │         │         ├─ PredictionWfst per category
     │         │         │     │
     │         │         │     ├─ TransducerCascade.run()
     │         │         │     │     ├─ WeightNormalization
     │         │         │     │     ├─ DeadStateElimination
     │         │         │     │     └─ StateMinimization
     │         │         │     │
     │         │         │     ├─ predict() → weight-ordered arms
     │         │         │     ├─ BooleanWeight → dead rules
     │         │         │     └─ CountingWeight → ambiguity warnings
     │         │         │
     │         │         ├─ RecoveryWfst per category
     │         │         │     ├─ sync tokens from FOLLOW sets
     │         │         │     └─ ContextWeight follow tightening
     │         │         │
     │         │         └─ DeadRuleWarnings
     │         │
     │         ├──▶ collect_dead_rule_labels()  ◀── Tier 1-4 analysis
     │         │         │
     │         │         └─ Dead code elimination: skip codegen
     │         │
     │         ├──▶ run_lints()  ──▶ 28 lints, compiler-style output
     │         │
     │         └──▶ Codegen
     │               │
     │               ├─ write_category_dispatch()
     │               │     └─ match arms ordered by tropical weight
     │               │
     │               ├─ write_trampoline_parser()
     │               │     ├─ Frame_Cat enum
     │               │     ├─ Thread-local pools
     │               │     └─ NFA spillover buffers
     │               │
     │               ├─ write_pratt_parser()
     │               │     ├─ BP lookup tables
     │               │     └─ make_infix / make_postfix
     │               │
     │               └─ emit_prediction_wfst_static()
     │                     └─ CSR flat arrays (compile-time constant)
     │
     └──▶ TokenStream (generated Rust code)
```

### Zero Runtime Overhead

All WFST computation happens at compile time. The generated parser carries:

1. **Static CSR arrays** — the WFST's adjacency structure, serialized as
   `&[u32]` and `&[f64]` constants for runtime reconstruction if needed
2. **Match arm ordering** — dispatch arms are emitted in weight-ascending order,
   so the hot path (cheapest alternative) is always tried first
3. **IS_ACCEPTING bitmap** — a `u128` or `&[bool]` constant for O(1) DFA
   acceptance checks in the lexer inner loop

No runtime semiring computation, no dynamic graph traversal, no heap allocation
for dispatch. The WFST's influence is entirely baked into code structure.

> **Cross-references:**
> [design/architecture-overview.md](architecture-overview.md) ·
> [architecture/wfst/pipeline-integration.md](../architecture/wfst/pipeline-integration.md) ·
> [architecture/data-flow.md](../architecture/data-flow.md) ·
> [architecture/generated-code-anatomy.md](../architecture/generated-code-anatomy.md)

---

## §12 A Complete Worked Example

This section traces a Calculator grammar through the full pipeline to show how
every component interacts.

### Grammar Fragment

```
category Int:
  ParseInt:    int_lit
  Negate:      Minus inner:Int        // unary prefix
  GroupExpr:   LParen inner:Int RParen
  infix Add:   Plus      left assoc precedence 1
  infix Mul:   Star      left assoc precedence 2
  infix Pow:   Caret     right assoc precedence 3
```

### Step 1: WFST Construction for `Int`

The pipeline builds a `PredictionWfst` for the `Int` category:

```
Dispatch WFST for Int
──────────┬────────────┬────────────────────────
Token     │ Action     │ Weight (tropical)
──────────┼────────────┼────────────────────────
IntLit    │ ParseInt   │ 0.0   (unique dispatch)
LParen    │ GroupExpr  │ 0.5   (grouping)
Minus     │ Negate     │ 1.0   (unary prefix)
```

After `TransducerCascade` (WeightNorm → DeadStateElim → StateMin):
- 3 states → 2 states (start + accept)
- Weights normalized: best action = 0.0 ✓

### Step 2: BooleanWeight Dead-Rule Check

```
  forward<BooleanWeight>(wfst, "IntLit")  = true   → ParseInt alive
  forward<BooleanWeight>(wfst, "LParen")  = true   → GroupExpr alive
  forward<BooleanWeight>(wfst, "Minus")   = true   → Negate alive
  forward<BooleanWeight>(wfst, "FloatLit")= false   → (no rule dispatches here)

  Result: 0 dead rules in Int category ✓
```

### Step 3: CountingWeight Ambiguity Detection

```
  forward<CountingWeight>(wfst, "IntLit")  = 1   → unambiguous ✓
  forward<CountingWeight>(wfst, "LParen")  = 1   → unambiguous ✓
  forward<CountingWeight>(wfst, "Minus")   = 1   → unambiguous ✓

  No ambiguity warnings emitted ✓
```

If a second rule also dispatched on `Minus` (e.g., `SubExpr: Minus inner:Int`),
the counting weight would be 2, triggering lint `W03: high-ambiguity-token`.

### Step 4: Error Recovery for `1 + + 2`

Input: `IntLit(1) Plus Plus IntLit(2)`

```
  Parsing: parse_Int(min_bp=0)
    NUD: IntLit(1) → Int(1)                     ✓
    LED: Plus, bp=(2,3), 2 ≥ 0 → consume        ✓
      NUD: Plus ← ERROR: expected IntLit/LParen/Minus, got Plus

  Recovery WFST evaluation:
    Option A: Skip(Plus), parse IntLit(2)        cost = 0.5
    Option B: Insert(IntLit(0)), parse Plus      cost = 2.0
    Option C: Delete(Plus), parse IntLit(2)      cost = 1.0

  Viterbi selects: Option A (Skip), cost = 0.5
  Result: Add(Int(1), Int(2)) with recovery diagnostic
```

### Step 5: Trampoline Frame Sequence for `1 + 2 * 3`

```
  parse_Int_own(tokens, pos=0, min_bp=0):
    frames: []

    NUD: IntLit(1) → lhs = Int(1)

    LED: Plus, bp=(2,3), 2 ≥ 0
      frames.push(InfixRHS { lhs: Int(1), op_pos: 1, saved_bp: 3 })
      min_bp ← 3
      continue 'drive                    // no recursion!

    NUD: IntLit(2) → lhs = Int(2)

    LED: Star, bp=(4,5), 4 ≥ 3
      frames.push(InfixRHS { lhs: Int(2), op_pos: 3, saved_bp: 5 })
      min_bp ← 5
      continue 'drive

    NUD: IntLit(3) → lhs = Int(3)

    LED: Eof, no bp → break 'led
      frames.pop() → InfixRHS { lhs: Int(2), op_pos: 3 (Star) }
      lhs ← Mul(Int(2), Int(3))

    LED: Eof, no bp → break 'led
      frames.pop() → InfixRHS { lhs: Int(1), op_pos: 1 (Plus) }
      lhs ← Add(Int(1), Mul(Int(2), Int(3)))

    frames.is_empty() → break 'drive

  Result: Add(Int(1), Mul(Int(2), Int(3)))  ✓
```

No recursive call was made. The two `InfixRHS` frames replaced what would have
been two levels of OS stack depth. The frame vector is returned to the
thread-local pool for reuse by the next parse call.

---

## §13 Conclusion and Design Principles

PraTTaIL's design is guided by five principles:

### 1. Algebraic, Not Heuristic

Every dispatch decision, recovery action, and optimization pass has an algebraic
foundation in semiring theory. Dispatch ordering follows from tropical shortest
paths. Dead-rule detection follows from boolean reachability. Recovery follows
from minimum edit distance. These are not heuristics that might fail on edge
cases — they are provably optimal within their semiring's definition of "optimal."

### 2. Unified, Not Fragmented

One data structure (the WFST) serves six roles: dispatch, dead-rule detection,
ambiguity quantification, error recovery, optimization, and grammar composition.
Traditional parser generators use separate data structures for each concern,
leading to inconsistencies and maintenance burden.

### 3. Generated, Not Hand-Written

PraTTaIL is a **compile-time code generator**. The grammar author specifies
categories, rules, and operators; the framework generates optimized Rust code
with weight-ordered dispatch, stack-safe trampoline parsing, and static WFST
data. No hand-written parser code is needed.

### 4. Stack-Safe, Not Stack-Dependent

The trampoline architecture eliminates OS stack overflow for deeply nested
expressions while improving performance for flat expressions through frame pool
reuse. Parsing depth is limited only by available heap memory.

### 5. Composable, Not Monolithic

Grammar composition via weighted WFST union allows independently developed
grammars to be combined with algebraically sound weight arbitration. The
composition lint suite (X01–X05) catches interaction bugs at compile time.

---

## §14 References and Cross-References

### Internal Documentation

**Design:**
- [Architecture Overview](architecture-overview.md)
- [Pratt Generator](pratt-generator.md)
- [Composed Dispatch](composed-dispatch.md)
- [Lint Layer](lint-layer.md)
- [Parser-Driven Lexing](parser-driven-lexing.md) (historical)

**Design — WFST:**
- [Dead-Rule Detection](wfst/dead-rule-detection.md)
- [Error Recovery](wfst/error-recovery.md)
- [Recovery Config](wfst/recovery-config.md)
- [Token Lattices](wfst/token-lattices.md)
- [Prediction](wfst/prediction.md)
- [Grammar Composition](wfst/grammar-composition.md)
- [NFA Disambiguation](wfst/nfa-disambiguation.md)

**Design — Semirings:**
- [Boolean](wfst/semirings/boolean-weight.md) ·
  [Counting](wfst/semirings/counting-weight.md) ·
  [Edit](wfst/semirings/edit-weight.md) ·
  [Context](wfst/semirings/context-weight.md) ·
  [Complexity](wfst/semirings/complexity-weight.md)
- [Tropical](wfst/semirings/tropical-weight.md) ·
  [Log](wfst/semirings/log-weight.md) ·
  [Product](wfst/semirings/product-weight.md) ·
  [Entropy](wfst/semirings/entropy-weight.md) ·
  [N-best](wfst/semirings/nbest-weight.md)

**Design — Disambiguation:**
- [Lexical Disambiguation](disambiguation/01-lexical-disambiguation.md)
- [Parse Prediction](disambiguation/02-parse-prediction.md)
- [Operator Precedence](disambiguation/03-operator-precedence.md)
- [Cross-Category Resolution](disambiguation/04-cross-category-resolution.md)
- [Error Recovery](disambiguation/05-error-recovery.md)
- [Layer Interactions](disambiguation/06-layer-interactions.md)
- [Semantic Disambiguation](disambiguation/07-semantic-disambiguation.md)
- [NFA-WFST Disambiguation](disambiguation/08-nfa-wfst-disambiguation.md)

**Theory:**
- [Pratt Parsing](../theory/pratt-parsing.md)
- [Finite Automata](../theory/finite-automata.md)
- [Parsing Landscape](../theory/parsing-landscape.md)
- [Weighted Automata](../theory/wfst/weighted-automata.md)
- [Semirings](../theory/wfst/semirings.md)
- [Viterbi and Forward-Backward](../theory/wfst/viterbi-and-forward-backward.md)

**Architecture:**
- [Crate Structure](../architecture/crate-structure.md)
- [Data Flow](../architecture/data-flow.md)
- [Generated Code Anatomy](../architecture/generated-code-anatomy.md)
- [Pipeline Integration](../architecture/wfst/pipeline-integration.md)
- [NFA Spillover Architecture](../architecture/wfst/nfa-spillover-architecture.md)
- [Optimization Pipeline](../architecture/wfst/optimization-pipeline.md)
- [Module Map](../architecture/wfst/module-map.md)

**Optimization:**
- [Optimization README](../optimization/README.md)
- [Completed Sprints](../optimization/completed-sprints.md)

### External References

1. Pratt, V. R. (1973). "Top down operator precedence." *Proceedings of the 1st
   Annual ACM SIGACT-SIGPLAN Symposium on Principles of Programming Languages*,
   pp. 41–51.

2. Mohri, M., Pereira, F., & Riley, M. (2002). "Weighted finite-state
   transducers in speech recognition." *Computer Speech & Language*, 16(1),
   pp. 69–88.

3. Allauzen, C., Riley, M., Schalkwyk, J., Skut, W., & Mohri, M. (2007).
   "OpenFst: A general and efficient weighted finite-state transducer library."
   *Proceedings of the 12th International Conference on Implementation and
   Application of Automata (CIAA)*, pp. 11–23.

4. Kuich, W., & Salomaa, A. (1986). *Semirings, Automata, Languages*. EATCS
   Monographs on Theoretical Computer Science, Vol. 5. Springer.

5. Viterbi, A. (1967). "Error bounds for convolutional codes and an
   asymptotically optimum decoding algorithm." *IEEE Transactions on Information
   Theory*, 13(2), pp. 260–269.
