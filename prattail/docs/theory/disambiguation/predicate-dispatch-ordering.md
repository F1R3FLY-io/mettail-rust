# Most-Specific-First Dispatch via Guard Subsumption

## 1. Motivation

When multiple grammar rules match the same leading token, the parser must decide which rule to try first. This is the classic **multimethod dispatch** problem applied to grammar predicates: given a set of overlapping guard predicates, find an ordering that respects specificity — more specific predicates (matching fewer inputs) should be tried before more general ones (matching more inputs).

Ernst, Kaplan, and Chambers (1998) showed that most-specific-first ordering is correct when the predicate lattice has no ambiguous overlap (no two predicates are incomparable and overlapping). This document formalizes predicate subsumption, defines the specificity score, proves correctness of the ordering, and derives the `order_by_specificity` implementation in `predicate_dispatch.rs`.

## 2. Definitions

**Definition 5.1** (Predicate Subsumption). Let p and q be guard predicates with associated languages L(p), L(q) ⊆ Σ (sets of tokens matched). Predicate p is **subsumed by** q (written p ≺ q) iff

    L(p) ⊂ L(q)    (strict subset)

Equivalently, every token matched by p is also matched by q, and q matches at least one token that p does not.

*Example*: If p matches {"if"} and q matches {"if", "unless"}, then L(p) = {"if"} ⊂ {"if", "unless"} = L(q), so p ≺ q.

*Non-example*: If p matches {"if", "while"} and q matches {"if", "for"}, then neither L(p) ⊂ L(q) nor L(q) ⊂ L(p). The predicates are **incomparable** and their overlap on {"if"} requires explicit disambiguation.

**Definition 5.2** (Specificity Score). For a predicate p with label l, the **specificity score** is

    spec(p) = |{ (a, b) ∈ subsumed_guards : a = l }|

That is, the number of subsumption pairs in which p appears as the *subsumed* element (the more specific side). A higher specificity score means more predicates are strictly more general than p, confirming that p is highly specific.

*Intuition*: If p is subsumed by 3 other predicates, spec(p) = 3. If p subsumes others but is not itself subsumed by anything, spec(p) = 0.

**Definition 5.3** (Most-Specific-First Ordering). Given a list of predicate labels L = [l₁, ..., lₙ] and their specificity scores, the **most-specific-first ordering** is a permutation π of L such that:

    spec(π(i)) ≥ spec(π(i+1))    for all 1 ≤ i < n

with ties broken by **grammar order**: if spec(π(i)) = spec(π(j)) and i < j in the original list L, then π(i) appears before π(j) in the output.

## 3. Theorems

**Theorem 5.1** (Correctness of Most-Specific-First Dispatch; Ernst, Kaplan, & Chambers, 1998). *Let P = {p₁, ..., pₙ} be a set of guard predicates forming a partial order under subsumption (≺). If for every pair pᵢ, pⱼ with L(pᵢ) ∩ L(pⱼ) ≠ ∅, either pᵢ ≺ pⱼ, pⱼ ≺ pᵢ, or pᵢ = pⱼ (no ambiguous overlap), then the most-specific-first ordering is correct: the first applicable predicate in the ordering is the unique most-specific match.*

*Discussion.* Ernst et al. formalized this as Theorem 3.1 in their ECOOP 1998 paper. The proof relies on the partial order being a **lattice** over the overlapping region: for any two overlapping predicates, there must exist a greatest lower bound (their intersection) that is also a predicate in P, or one must subsume the other.

In the grammar context, the "no ambiguous overlap" condition is the absence of two rules with incomparable overlapping guards within the same category. When this condition fails, the SYM01 lint fires to warn the grammar author.

*Reference*: Ernst, M., Kaplan, C., & Chambers, C. (1998). "Predicate Dispatching: A Unified Theory of Dispatch." *ECOOP*, LNCS 1445, pp. 186–211. Springer.

**Theorem 5.2** (Preservation). *The function `order_by_specificity` returns a permutation of its input: every input label appears exactly once in the output, and no labels are added or removed.*

*Proof.* The implementation proceeds as follows:

1. All input labels are inserted into the indexed list: `indexed = [(0, l₁), (1, l₂), ..., (n-1, lₙ)]`.
2. A stable sort is applied to `indexed` by descending specificity score with ascending index tiebreak.
3. The sorted list is mapped to extract labels: `output = [indexed[0].1, indexed[1].1, ..., indexed[n-1].1]`.

A stable sort is a permutation of its input — it rearranges elements without adding or removing any. Therefore, the output contains exactly the same multiset of labels as the input. Since the input labels are distinct (each rule has a unique label), the output is a permutation. ∎

**Theorem 5.3** (Grammar Order Tiebreak Safety). *When two predicates have equal specificity scores, preserving their original grammar order is a safe tiebreak strategy.*

*Proof.* Equal specificity means spec(pᵢ) = spec(pⱼ): both predicates are subsumed by the same number of other predicates. This arises in two situations:

**Case 1**: pᵢ and pⱼ have disjoint guard sets (L(pᵢ) ∩ L(pⱼ) = ∅). Their order is immaterial since no input token activates both — the parser will try each in turn and only one can match. Grammar order is a neutral choice.

**Case 2**: pᵢ and pⱼ have identical guard sets (L(pᵢ) = L(pⱼ)). Neither subsumes the other (strict subset is required), so spec is equal. The SYM01 lint flags this as an ambiguous overlap. Grammar order preserves the programmer's intent: the first-written rule takes priority, matching the "first match wins" convention common in pattern matching.

In both cases, grammar order does not introduce unsoundness. It is a design choice that respects programmer expectations. ∎

## 4. Algorithm

### Algorithm 5: order_by_specificity

```
PROCEDURE ORDER-BY-SPECIFICITY(predicate_labels, subsumed_guards)
  INPUT:  predicate_labels = [l₁, l₂, ..., lₙ]  — rule labels in grammar order
          subsumed_guards = [(lₐ, l_b), ...]     — pairs where lₐ ≺ l_b
  OUTPUT: Permutation of predicate_labels sorted by descending specificity

  1. // Early exit: no subsumption data → preserve grammar order
     IF subsumed_guards is empty THEN
       RETURN predicate_labels

  2. // Build specificity scores
     specificity ← {}
     FOR EACH l IN predicate_labels:
       specificity[l] ← 0

     FOR EACH (lₐ, l_b) IN subsumed_guards:
       // lₐ is more specific (subsumed by l_b)
       IF lₐ ∈ specificity THEN
         specificity[lₐ] ← specificity[lₐ] + 1

  3. // Create indexed list for stable sort
     indexed ← [(0, l₁), (1, l₂), ..., (n-1, lₙ)]

  4. // Sort: descending specificity, ascending index for ties
     STABLE-SORT indexed BY:
       PRIMARY: specificity[lⱼ] DESCENDING
       SECONDARY: index ASCENDING

  5. // Extract labels
     RETURN [indexed[0].1, indexed[1].1, ..., indexed[n-1].1]

  COMPLEXITY: O(n log n + s) where n = |predicate_labels|, s = |subsumed_guards|
```

## 5. Worked Example

### Diamond Subsumption Lattice

Consider a grammar with four predicates for pattern matching:

```
Match ::= "(" IDENT ")"        (rule A: parenthesized identifier)
        | "(" Expr ")"         (rule B: parenthesized expression)
        | "(" Expr "," Expr ")"  (rule C: parenthesized pair)
        | Expr                  (rule D: bare expression)
```

**Guard extraction**:
- G(A) = {"("}
- G(B) = {"("}
- G(C) = {"("}
- G(D) = (all expression-starting tokens)

**Subsumption analysis** (based on deeper structural analysis, not just FIRST sets):

Suppose deeper analysis yields:
- L(A) ⊂ L(B): every parenthesized identifier is a parenthesized expression.
- L(A) ⊂ L(D): every parenthesized identifier is an expression.
- L(B) ⊂ L(D): every parenthesized expression is an expression.
- L(C) ⊂ L(D): every parenthesized pair is an expression.
- L(C) and L(B) are incomparable: a pair is not a single expression, and a single expression is not a pair.

Subsumption pairs:
```
subsumed_guards = [
  (A, B),   // A ≺ B
  (A, D),   // A ≺ D
  (B, D),   // B ≺ D
  (C, D),   // C ≺ D
]
```

**Step 1: Specificity scores**

| Predicate | Subsumed-by count | spec |
|-----------|-------------------|------|
| A         | B, D              | 2    |
| B         | D                 | 1    |
| C         | D                 | 1    |
| D         | (none)            | 0    |

**Step 2: Sort by descending specificity**

- A (spec = 2)
- B (spec = 1), C (spec = 1) — tie broken by grammar order: B before C
- D (spec = 0)

**Result**: [A, B, C, D]

The parser tries A first (most specific), then B and C (intermediate), then D (most general). This ensures that the most precise match is attempted before falling back to broader alternatives.

## 6. Diagram

### Subsumption Lattice (Hasse Diagram)

```
                         D (most general)
                        ╱ ╲
                       ╱   ╲
                      ╱     ╲
                     B       C
                    ╱
                   ╱
                  A (most specific)

  Partial order (≺):
    A ≺ B ≺ D
    A ≺ D (transitive)
    C ≺ D
    B ∥ C (incomparable — ambiguous overlap on "(")

  Dispatch order: A → B → C → D
  (B before C by grammar-order tiebreak)
```

### Specificity Score Computation

```
  subsumed_guards:       Specificity increments:

  (A, B)  →  spec[A] += 1     A: ██ = 2
  (A, D)  →  spec[A] += 1     B: █  = 1
  (B, D)  →  spec[B] += 1     C: █  = 1
  (C, D)  →  spec[C] += 1     D:    = 0

  Sorted order (descending spec, grammar-order tiebreak):

  ┌────┬──────┬───────────────────────────────┐
  │ Pos│ Label│ spec │ Rationale              │
  ├────┼──────┼──────┼────────────────────────┤
  │  1 │  A   │  2   │ most specific          │
  │  2 │  B   │  1   │ intermediate (tied)    │
  │  3 │  C   │  1   │ intermediate (tied)    │
  │  4 │  D   │  0   │ most general (fallback)│
  └────┴──────┴──────┴────────────────────────┘
```

### Dispatch Decision Tree

```
  Input token: "("
  ┌──────────────────────────────────────────┐
  │ Try rule A: "(" IDENT ")"                │
  │   ├─ Success → return A's parse tree     │
  │   └─ Failure ↓                           │
  │ Try rule B: "(" Expr ")"                 │
  │   ├─ Success → return B's parse tree     │
  │   └─ Failure ↓                           │
  │ Try rule C: "(" Expr "," Expr ")"        │
  │   ├─ Success → return C's parse tree     │
  │   └─ Failure ↓                           │
  │ Try rule D: Expr                         │
  │   ├─ Success → return D's parse tree     │
  │   └─ Failure → parse error               │
  └──────────────────────────────────────────┘

  Key insight: A ≺ B ≺ D, so trying A before B before D
  is safe — every input matching A also matches B and D.
```

## 7. Comparison with Classical Multimethod Dispatch

The predicate dispatch ordering in PraTTaIL is a specialization of the general predicate dispatch framework:

| Concept                  | General (Ernst et al.) | PraTTaIL                        |
|--------------------------|------------------------|----------------------------------|
| Predicate domain         | Arbitrary types        | Token sets (FIRST sets)          |
| Subsumption              | Subtype relation       | Strict set containment           |
| Specificity              | Lattice depth          | Subsumption count                |
| Ambiguity resolution     | Error / linearization  | Grammar-order tiebreak + SYM01 lint |
| Runtime dispatch         | Dynamic vtable lookup  | Compile-time rule ordering       |

The key simplification in PraTTaIL is that dispatch happens at compile time: the `order_by_specificity` function produces a static ordering that is baked into the generated parser. No runtime dispatch overhead is incurred.

## 8. Implementation References

- **`order_by_specificity()`** — `predicate_dispatch.rs:1188`: Core function. Takes predicate labels and subsumption pairs, returns labels sorted by descending specificity with grammar-order tiebreak.
- **`SymbolicAnalysis::subsumed_guards`** — `symbolic.rs`: The subsumption pairs consumed by `order_by_specificity`. Computed by `analyze_from_bundle()`.
- **`DispatchPlan`** — `predicate_dispatch.rs`: Orchestrates multi-module dispatch including specificity ordering.
- **`PredefinedDispatchCompiler`** — `predicate_dispatch.rs`: Compiler adapter integrating guard analysis, SCC analysis, and specificity ordering into the dispatch pipeline.

## 9. Cross-References

- `theory/disambiguation/symbolic-guard-algebra.md` — Guard extraction and subsumption detection (input to this module)
- `theory/disambiguation/buchi-scc-liveness.md` — SCC analysis for recursive context detection (orthogonal)
- `theory/disambiguation/information-theoretic-dispatch.md` — Entropy-based beam width scaling (complementary)
- `theory/dispatch/variety-classification.md` — Algebraic variety theory for grammar classification
- `docs/diagnostics/predicate-dispatch/PD01.md` — PD01 lint: ambiguous predicate overlap
- `docs/diagnostics/symbolic/SYM01.md` — SYM01 lint: overlapping guards requiring disambiguation

## 10. Bibliography

1. Ernst, M., Kaplan, C., & Chambers, C. (1998). "Predicate Dispatching: A Unified Theory of Dispatch." *European Conference on Object-Oriented Programming (ECOOP)*, LNCS 1445, pp. 186–211. Springer.

2. Chambers, C. & Chen, W. (1999). "Efficient Multiple and Predicate Dispatching." *OOPSLA*, pp. 238–255. ACM.

3. Castagna, G. (1995). "Covariance and Contravariance: Conflict without a Cause." *ACM Trans. Programming Languages and Systems*, 17(3), pp. 431–447.

4. D'Antoni, L. & Veanes, M. (2017). "The Power of Symbolic Automata and Transducers." *Computer Aided Verification (CAV)*, LNCS 10427, pp. 47–67. Springer.
