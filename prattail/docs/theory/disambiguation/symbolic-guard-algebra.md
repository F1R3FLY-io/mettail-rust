# Guard Extraction, Overlap, and Subsumption via Symbolic Finite Automata

## 1. Motivation

Pratt parsing dispatches on the leading token of each rule alternative. When two rules in the same category can both fire on the same leading token, the parser must either backtrack (expensive) or apply an explicit disambiguation strategy. **Guard extraction** lifts the FIRST-set computation into the symbolic automata framework, enabling compile-time detection of ambiguous overlaps and safe reordering via subsumption analysis.

This document formalizes guard predicates, defines overlap and subsumption relations, proves that overlap implies potential ambiguity, and demonstrates that subsumption-based priority ordering is safe.

## 2. Definitions

**Definition 2.1** (Guard Predicate). For a grammar rule r with body β = s₁ s₂ ... sₖ (a sequence of syntax items), the **guard predicate** G(r) is the set of tokens that can appear as the leading terminal:

    G(r) = { t ∈ Σ : t is a possible first terminal of β }

Formally, G(r) is defined by structural recursion on the first syntax item s₁:
- If s₁ = Terminal(t): G(r) = {t}
- If s₁ = NonTerminal(C): G(r) = ⋃_{r' ∈ rules(C)} G(r')
- If s₁ = IdentCapture or s₁ = Binder: G(r) = Σ_ident (the set of all identifier-class tokens)
- If s₁ = Optional{inner}: G(r) = G(inner) ∪ FIRST(s₂...sₖ) (the optional may be skipped)
- If s₁ = Collection or s₁ = Map or s₁ = Zip or s₁ = Sep: G(r) = ∅ (structurally unsatisfiable as leading item)

*Remark.* In MeTTaIL, guard extraction is restricted to the **first** syntax item of each rule. This is sound because Pratt parsing dispatches on the current token — deeper lookahead is handled by the parser's recursive descent, not by the guard.

**Definition 2.2** (Guard Overlap). Two rules r₁, r₂ belonging to the same category C have **overlapping guards** iff

    G(r₁) ∩ G(r₂) ≠ ∅

That is, there exists at least one token t that could serve as the leading terminal for both rules.

**Definition 2.3** (Guard Subsumption). Rule r₁ is **subsumed by** rule r₂ (written r₁ ≺ r₂) iff

    G(r₁) ⊂ G(r₂)    (strict subset)

Equivalently, every leading token of r₁ is also a leading token of r₂, but r₂ accepts additional leading tokens that r₁ does not.

**Definition 2.4** (Guard Satisfiability). A rule r is **satisfiable** iff there exists some token that can initiate a parse of r:

    satisfiable(r) ⟺ G(r) ≠ ∅ ∨ starts_with_nonterminal(r) ∨ starts_with_ident_capture(r) ∨ starts_with_binder(r)

Rules that are unsatisfiable (G(r) = ∅ and no non-terminal/ident/binder start) are dead code — they can never match any input.

## 3. Theorems

**Theorem 2.1** (Overlap Implies Potential Ambiguity). *Let r₁, r₂ be distinct rules in the same category C with overlapping guards: G(r₁) ∩ G(r₂) ≠ ∅. Then there exists a token t such that both r₁ and r₂ are applicable when t is the current lookahead. Without additional disambiguation, the parser must either backtrack or non-deterministically choose between r₁ and r₂.*

*Proof.* By Definition 2.2, there exists t ∈ G(r₁) ∩ G(r₂). By Definition 2.1, t is a possible leading terminal for both r₁ and r₂. In Pratt parsing, the parser at a `nud` position dispatches on the current token. When the current token is t and the active category is C, both r₁ and r₂ are candidates. The parser cannot know which rule will ultimately succeed without attempting to parse both (or applying a priority rule). Therefore, either:

(a) The parser tries r₁ first, and if it fails, backtracks to try r₂ (or vice versa), or
(b) An explicit priority ordering determines which rule is tried first.

In both cases, the overlap creates a disambiguation obligation. ∎

**Theorem 2.2** (Subsumption Implies Safe Priority). *Let r₁, r₂ be rules in the same category C with G(r₁) ⊂ G(r₂) (r₁ is subsumed by r₂). Then trying r₁ before r₂ is safe: for every token t ∈ G(r₁), t ∈ G(r₂) as well, so falling back to r₂ after r₁ fails loses no matches.*

*Proof.* Suppose the parser encounters token t and tries r₁ first:

- **Case 1**: t ∈ G(r₁). The parser attempts r₁. If r₁ succeeds, the parse is complete. If r₁ fails (because deeper structure does not match), the parser falls back to r₂. Since G(r₁) ⊂ G(r₂), we have t ∈ G(r₂), so r₂ is also applicable and may succeed.

- **Case 2**: t ∉ G(r₁) but t ∈ G(r₂). The parser skips r₁ (guard not satisfied) and proceeds directly to r₂.

In neither case does the priority ordering cause a valid parse to be missed. The converse ordering (r₂ before r₁) could mask r₁ entirely, since every token matching r₁ also matches r₂. Therefore, "most specific first" is the safe ordering. ∎

**Theorem 2.3** (Guard Extraction Completeness for Terminal-Started Rules). *For any rule r whose first syntax item is a Terminal(t), the guard extraction yields G(r) = {t}. This is exactly the FIRST set of r restricted to terminals.*

*Proof.* By structural induction on SyntaxItemSpec:

**Base case**: If the first item is Terminal(t), then by definition G(r) = {t}. The FIRST set of a terminal-started production is {t} by the standard FIRST set construction (Aho, Sethi, Ullman, 1986, Def. 4.4). These coincide.

**Inductive case**: If the first item is NonTerminal(C), then G(r) = ⋃_{r' ∈ rules(C)} G(r'). By the inductive hypothesis, each G(r') is correct for r'. The union is the standard FIRST(C) computation. If the first item is Optional{inner}, then G(r) = G(inner) ∪ FIRST(rest), matching the nullable-symbol FIRST set rule.

For IdentCapture and Binder starts, the guard is the (potentially infinite) set of identifier tokens, which cannot be enumerated finitely but is correctly handled by the satisfiability check (Definition 2.4). ∎

*Remark.* Completeness holds only for the leading position. Guard extraction does not compute the full FIRST set for rules requiring multi-token lookahead — that is delegated to the prediction module's FIRST/FOLLOW analysis.

## 4. Algorithm

### Algorithm 2: Guard Extraction, Overlap Detection, and Subsumption Detection

```
PROCEDURE ANALYZE-GUARDS(all_syntax, categories)
  INPUT:  all_syntax = [(cat, label, items)]  — all grammar rules
          categories = [CategoryInfo]          — category metadata
  OUTPUT: SymbolicAnalysis = {
            guard_satisfiability: [(label, bool)],
            overlapping_guards: [(label₁, label₂)],
            subsumed_guards: [(label_sub, label_sup)],
            unsatisfiable_rule_labels: [label]
          }

  1. // Phase 1: Extract guard sets
     FOR EACH rule (cat, label, items) IN all_syntax:
       guard[label] ← EXTRACT-GUARD(items)
       satisfiable[label] ← (guard[label] ≠ ∅) ∨ starts_nonterm(items)
                             ∨ starts_ident(items) ∨ starts_binder(items)

  2. // Phase 2: Group by category
     FOR EACH category C IN categories:
       rules_C ← { (label, guard[label]) : cat = C.name }

  3. // Phase 3: Detect overlaps (same category only)
     overlaps ← ∅
     FOR EACH category C:
       FOR EACH pair (r₁, r₂) IN rules_C × rules_C WHERE r₁ ≠ r₂:
         IF guard[r₁] ∩ guard[r₂] ≠ ∅ THEN
           overlaps ← overlaps ∪ {(r₁, r₂)}

  4. // Phase 4: Detect subsumptions
     subsumed ← ∅
     FOR EACH category C:
       FOR EACH pair (r₁, r₂) IN rules_C × rules_C WHERE r₁ ≠ r₂:
         IF guard[r₁] ⊂ guard[r₂] THEN       // strict subset
           subsumed ← subsumed ∪ {(r₁, r₂)}  // r₁ subsumed by r₂

  5. RETURN (satisfiable, overlaps, subsumed, {l : ¬satisfiable[l]})

  COMPLEXITY: O(R² × T) where R = max rules per category, T = max guard set size

PROCEDURE EXTRACT-GUARD(items)
  IF items is empty THEN RETURN ∅  // but mark as satisfiable (epsilon)
  MATCH items[0]:
    Terminal(t)     → RETURN {t}
    NonTerminal(_)  → RETURN ∅     // satisfiable via non-terminal expansion
    IdentCapture(_) → RETURN ∅     // satisfiable via identifier class
    Binder(_)       → RETURN ∅     // satisfiable via binder class
    Optional{inner} → RETURN EXTRACT-GUARD([inner]) ∪ EXTRACT-GUARD(items[1..])
    Collection(_)   → RETURN ∅     // unsatisfiable as leading item
    Map(_)          → RETURN ∅     // unsatisfiable as leading item
    _               → RETURN ∅
```

## 5. Worked Example

Consider an if-then / if-then-else grammar:

```
Stmt ::= "if" Expr "then" Stmt                  (rule r₁: IfThen)
       | "if" Expr "then" Stmt "else" Stmt       (rule r₂: IfThenElse)
       | IDENT ":=" Expr                         (rule r₃: Assign)
       | "while" Expr "do" Stmt                  (rule r₄: While)
```

**Guard extraction**:
- G(r₁) = {"if"}
- G(r₂) = {"if"}
- G(r₃) = ∅ (starts with IdentCapture, satisfiable but no terminal guard)
- G(r₄) = {"while"}

**Overlap detection**:
- G(r₁) ∩ G(r₂) = {"if"} ≠ ∅ — **overlap detected** (SYM01 lint)
- G(r₁) ∩ G(r₄) = ∅ — no overlap
- G(r₂) ∩ G(r₄) = ∅ — no overlap

**Subsumption detection**:
- G(r₁) = {"if"} = G(r₂) — neither is a strict subset of the other. No subsumption.
- If r₁ had guard {"if"} and r₂ had guard {"if", "unless"}, then G(r₁) ⊂ G(r₂), and r₁ would be subsumed by r₂. Trying r₁ first would be safe.

**Satisfiability**:
- r₁, r₂, r₄: satisfiable (terminal starts)
- r₃: satisfiable (IdentCapture start)
- No unsatisfiable rules in this grammar.

## 6. Diagram

### Guard Sets: Venn Diagram

```
  Category: Stmt
  ┌───────────────────────────────────────────────────────────┐
  │                     Σ (all tokens)                        │
  │                                                           │
  │   ┌─────────────────────────────────────────────┐         │
  │   │ G(r₁) = G(r₂) = {"if"}                     │         │
  │   │                                             │         │
  │   │    ┌───────────┐   ┌───────────┐            │         │
  │   │    │  G(r₁)    │   │  G(r₂)    │            │         │
  │   │    │  {"if"}   ├───┤  {"if"}   │            │         │
  │   │    │           │ ▓ │           │            │         │
  │   │    └───────────┘   └───────────┘            │         │
  │   │         ▓ = overlap region = {"if"}         │         │
  │   └─────────────────────────────────────────────┘         │
  │                                                           │
  │         ┌───────────┐        ┌───────────────┐            │
  │         │  G(r₄)    │        │  G(r₃)        │            │
  │         │ {"while"} │        │  (ident class) │            │
  │         └───────────┘        └───────────────┘            │
  │                                                           │
  │   No overlap between G(r₃), G(r₄), and the if-group.     │
  └───────────────────────────────────────────────────────────┘
```

### Subsumption Lattice Example

```
  Consider guards: G(A) = {"+"}, G(B) = {"+", "-"}, G(C) = {"+", "-", "*"}

  Subsumption partial order (Hasse diagram):

                    G(C) = {"+", "-", "*"}
                   ╱                        most general
                  ╱
           G(B) = {"+", "-"}
          ╱
         ╱
  G(A) = {"+"}                              most specific

  Ordering: try A first, then B, then C.
  Safe because G(A) ⊂ G(B) ⊂ G(C).
```

## 7. Connection to Symbolic Automata Theory

Guard predicates can be viewed as a restricted instance of symbolic finite automata (SFA). Each guard set G(r) is a unary predicate over the token alphabet Σ. The Boolean algebra operations on guards correspond to SFA operations:

| Guard operation    | SFA analogue         | Boolean algebra |
|-------------------|---------------------|-----------------|
| G(r₁) ∩ G(r₂)    | Product construction | φ₁ ∧ φ₂         |
| G(r₁) ∪ G(r₂)    | Union construction   | φ₁ ∨ φ₂         |
| Σ \ G(r)          | Complement           | ¬φ              |
| G(r) = ∅?         | Emptiness check      | SAT(φ)          |

The guard satisfiability check (Definition 2.4) is exactly the SFA emptiness check restricted to single-transition automata.

*Reference*: D'Antoni, L. & Veanes, M. (2017). "The Power of Symbolic Automata and Transducers." *CAV*, LNCS 10427, pp. 47–67.

## 8. Implementation References

- **`analyze_from_bundle()`** — `symbolic.rs:1686`: Entry point for guard extraction. Iterates over `all_syntax`, extracts leading terminals, computes per-category overlaps and subsumptions.
- **`SymbolicAnalysis`** — `symbolic.rs`: Result struct containing `guard_satisfiability`, `overlapping_guards`, `subsumed_guards`, `unsatisfiable_rule_labels`.
- **`SymbolicCompiler`** — `symbolic.rs:1788`: Compiler adapter wrapping `analyze_from_bundle()` for the predicate dispatch pipeline.
- **`BooleanAlgebra` trait** — `symbolic.rs`: Trait providing `is_satisfiable()`, `and()`, `or()`, `not()` for symbolic predicate manipulation.

## 9. Cross-References

- `theory/symbolic/boolean-algebra.md` — Effective Boolean algebra theory underlying SFA operations
- `theory/disambiguation/predicate-dispatch-ordering.md` — Uses subsumption data to order predicates
- `theory/disambiguation/information-theoretic-dispatch.md` — Entropy computation over guard distributions
- `docs/diagnostics/symbolic/SYM01.md` — SYM01 lint: overlapping guards detected
- `docs/diagnostics/symbolic/SYM02.md` — SYM02 lint: unsatisfiable guard (dead rule)

## 10. Bibliography

1. D'Antoni, L. & Veanes, M. (2017). "The Power of Symbolic Automata and Transducers." *Computer Aided Verification (CAV)*, LNCS 10427, pp. 47–67. Springer.

2. D'Antoni, L. & Veanes, M. (2014). "Minimization of Symbolic Automata." *Principles of Programming Languages (POPL)*, pp. 541–553. ACM.

3. Aho, A.V., Sethi, R. & Ullman, J.D. (1986). *Compilers: Principles, Techniques, and Tools.* Addison-Wesley. Definition 4.4 (FIRST sets).

4. Knuth, D.E. (1965). "On the Translation of Languages from Left to Right." *Information and Control*, 8(6), pp. 607–639.
