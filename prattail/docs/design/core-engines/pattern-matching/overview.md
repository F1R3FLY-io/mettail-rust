# Pattern Matching and Unification: Overview

PraTTaIL uses three distinct forms of pattern matching, each serving a different purpose in the architecture. This document provides the theoretical backdrop and connects to the implementation.

**Prerequisites:** Familiarity with the [triemaps-that-match](../triemaps-that-match/foundations.md) and [Ascent](../ascent-datalog/overview.md) foundations.

---

## 1. Three Kinds of Pattern Matching

### 1.1 Parse Dispatch (Compile-Time)

**When:** During macro expansion, to determine which parse rule to attempt given an input token.

**Mechanism:** PathMap decision tree. Token sequences are byte-encoded and inserted into a radix-256 trie. At runtime, the generated parser consults the trie-derived match arms to select a rule.

**Formalism:** Discrimination tree lookup (Sekar, Ramakrishnan & Voronkov, 2001). The input is a sequence of tokens (ground terms); the stored patterns are rule prefixes (also ground). The match is exact or prefix-based.

**Key property:** No variables in the lookup key. This is a simple trie walk.

**Detailed in:** [Decision Trees](../triemaps-that-match/decision-trees.md)

### 1.2 Term Matching (Runtime)

**When:** During Ascent fixed-point evaluation, when a rule's LHS pattern must be matched against a concrete term.

**Mechanism:** Generated `match_pattern()` functions. The `language!` macro generates per-category match functions that use an iterative work stack (no recursion) to decompose terms and extract bindings.

**Formalism:** One-directional matching. Given a pattern `p` and a ground term `t`, find a substitution σ such that:

```text
σ(p) = t
```

This is strictly one-directional: variables only appear in the pattern, not the term. The match either succeeds (yielding bindings) or fails.

**Key property:** O(|p|) time per match attempt. Stack-safe to 100K+ nesting depth.

**Detailed in:** [Structural Matching](structural-matching.md)

### 1.3 Unification (Runtime/Analysis)

**When:** During constraint theory evaluation, type inference, or custom logic rules that require bidirectional matching.

**Mechanism:** Martelli-Montanari unification algorithm implemented as a `ConstraintTheory` plugin.

**Formalism:** Bidirectional matching. Given two terms `s` and `t` (both may contain variables), find a substitution σ such that:

```text
σ(s) = σ(t)
```

Unlike one-directional matching, both sides may contain variables that must be simultaneously bound.

**Key property:** O(n · α(n)) amortized time with path compression.

**Detailed in:** [Unification](unification.md)

---

## 2. Theoretical Connections

| Theory | PraTTaIL implementation | Key reference |
|--------|------------------------|---------------|
| Discrimination trees | PathMap decision trees | Sekar et al. (2001) |
| Triemaps that match | PathMap pattern trie | Peyton Jones & Graf (2022) |
| Martelli-Montanari | `unification.rs` | Martelli & Montanari (1982) |
| LogicT fair backtracking | `logict.rs` | Kiselyov et al. (2005) |
| De Bruijn indices | `pattern_codec.rs` | de Bruijn (1972) |

### Relationship Between the Three Forms

```text
                        ┌─────────────────────┐
                        │   Pattern Variables  │
                        │   in the Key?        │
                        └────────┬────────────┘
                                 │
                    ┌────── No ──┤── Yes ──┐
                    │            │          │
                    ▼            │          ▼
            Parse Dispatch       │    ┌────────────┐
            (exact lookup)       │    │ Variables   │
                                 │    │ on both     │
                                 │    │ sides?      │
                                 │    └──┬──────┬──┘
                                 │       │      │
                                 │   No ─┘  Yes ┘
                                 │   │          │
                                 ▼   ▼          ▼
                           Term Matching   Unification
                          (one-directional) (bidirectional)
```

---

## 3. Stack Safety as a Design Principle

All three matching engines in PraTTaIL use **explicit work stacks** rather than recursion:

| Engine | Stack type | Pool |
|--------|-----------|------|
| Parse dispatch | `Vec<Frame_Cat>` (trampoline) | Thread-local `Cell<Vec<Frame_Cat>>` |
| Term matching | `Vec<MatchTask>` | Thread-local `Cell<Vec<MatchTask>>` |
| Unification | `Vec<(TermExpr, TermExpr)>` | Inline (no pool needed) |

### Why Explicit Stacks?

1. **Depth safety**: Recursive descent crashes at ~10K nesting depth (platform stack limit). Explicit stacks handle 100K+ nesting.
2. **Zero steady-state allocation**: Thread-local pools reuse stack buffers across invocations via `Cell::take()` / `Cell::set()`.
3. **Predictable performance**: No function call overhead per recursion level.

### Thread-Local Pool Protocol

```rust
thread_local! {
    static POOL: Cell<Vec<MatchTask>> = Cell::new(Vec::new());
}

fn match_pattern(pattern, term) -> Option<Bindings> {
    let mut stack = POOL.with(|p| p.take());  // Take buffer (O(1))
    stack.clear();
    stack.push(initial_task);

    while let Some(task) = stack.pop() {
        // ... process task, push sub-tasks ...
    }

    let result = /* extract bindings */;
    POOL.with(|p| p.set(stack));  // Return buffer (O(1))
    result
}
```

The pool contains no lifetime-bearing references (`op_pos: usize` instead of `&'a [T]`), enabling safe `Cell` storage without `unsafe` code.

---

## 4. Alpha-Equivalence Across All Forms

De Bruijn canonicalization (`pattern_codec.rs`) is the unifying concept across all three matching forms:

- **Parse dispatch**: Token encoding is position-based (not name-based), achieving a similar effect to De Bruijn for terminals.
- **Term matching**: Generated match arms are structure-based, not name-based. Variable bindings are extracted by position in the constructor.
- **Pattern trie**: Uses explicit De Bruijn encoding (NewVar/VarRef tags) for alpha-equivalence grouping.
- **Unification**: Variables are identified by index (`usize`), not name — an implicit form of De Bruijn numbering.

**Detailed in:** [De Bruijn Encoding](de-bruijn-encoding.md)

---

## References

1. **Sekar, R., Ramakrishnan, I. V. & Voronkov, A.** (2001). "Term Indexing." In *Handbook of Automated Reasoning*, Ch. 26, pp. 1853-1964. — Survey of discrimination trees, path indexing, and substitution trees.

2. **Peyton Jones, S. & Graf, S.** (2022/2024). "Triemaps that match." arXiv:2302.08775. — Trie-based maps keyed by syntax trees with matching lookup.

3. **Martelli, A. & Montanari, U.** (1982). "An Efficient Unification Algorithm." *ACM TOPLAS* 4(2), 258-282. — The foundational unification algorithm used in PraTTaIL.

4. **Kiselyov, O. et al.** (2005). "Backtracking, Interleaving, and Terminating Monad Transformers." *ICFP 2005*. — Fair backtracking search framework.

5. **de Bruijn, N. G.** (1972). "Lambda calculus notation with nameless dummies." *Indagationes Mathematicae* 75(5), 381-392. — Canonical variable representation for alpha-equivalence.

---

**Next:** [Structural Matching](structural-matching.md) — the iterative match engine generated by `language!`.
