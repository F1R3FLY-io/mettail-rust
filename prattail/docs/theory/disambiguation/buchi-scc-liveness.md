# SCCs, Grammar Recursion, and Liveness-Aware Recovery

## 1. Motivation

Recursive grammar categories form cycles in the category dependency graph: `Expr` may reference `Stmt`, which references `Expr` again. These cycles are the grammar-level analogue of accepting strongly connected components (SCCs) in Buchi automata — they represent infinite-state computations (in the automata-theoretic sense) or unbounded recursive descent (in the parsing sense).

When error recovery occurs inside a recursive loop, the recovery strategy should *preserve the loop structure*. Skipping tokens to escape a recursive context is more damaging than inserting a synthetic token to keep the recursion going, because escaping breaks the well-nested structure that the grammar expects. Conversely, inserting tokens in a non-recursive context may introduce spurious nesting.

This document formalizes the category dependency graph, defines accepting SCCs via Tarjan's algorithm, and proves the correctness of liveness-aware recovery cost modulation.

## 2. Definitions

**Definition 3.1** (Category Dependency Graph). Given a grammar with categories C₁, ..., Cₙ and rules R₁, ..., Rₘ, the **category dependency graph** is a directed graph G = (V, E) where:

- V = {C₁, ..., Cₙ} — one vertex per grammar category
- E = {(Cᵢ, Cⱼ) : ∃ rule r ∈ rules(Cᵢ) that contains NonTerminal(Cⱼ) in its body}

An edge (Cᵢ, Cⱼ) means "category Cᵢ directly depends on category Cⱼ" — parsing Cᵢ may require recursively parsing Cⱼ.

*Example*: For the grammar

    Expr ::= Atom | Expr "+" Expr | "(" Stmt ")"
    Stmt ::= Expr ";" | "if" Expr "then" Stmt
    Decl ::= "let" IDENT "=" Expr

the edges are: Expr → Atom, Expr → Expr (self-loop), Expr → Stmt, Stmt → Expr, Stmt → Stmt (self-loop), Decl → Expr. No edges lead to Decl from Expr or Stmt.

**Definition 3.2** (Strongly Connected Component). A **strongly connected component** (SCC) of G = (V, E) is a maximal subset S ⊆ V such that for every pair u, v ∈ S, there exists a directed path from u to v:

    ∀ u, v ∈ S : u ⇝ v    (reachability in both directions)

Maximality means no proper superset of S satisfies this property.

**Definition 3.3** (Accepting SCC). An SCC S is **accepting** iff:
- |S| > 1 (the SCC contains a non-trivial cycle), or
- S = {v} and (v, v) ∈ E (the singleton is self-referencing)

An accepting SCC represents a set of categories that participate in a recursive parsing loop. Trivial SCCs (singletons with no self-loop) are non-recursive.

*Remark.* The terminology "accepting" comes from Buchi automata, where an SCC is accepting if it contains an accepting state visited infinitely often. In the grammar context, "accepting" means the SCC enables unbounded recursive descent.

**Definition 3.4** (Liveness Multipliers). For a category C:
- If C belongs to an accepting SCC, the **InsertToken discount** is 0.7 and the **SkipToSync penalty** is 1.3.
- If C does not belong to an accepting SCC, both multipliers are 1.0 (neutral).

These multipliers modulate the base recovery cost to favor structure-preserving actions in recursive contexts.

## 3. Theorems

**Theorem 3.1** (Tarjan's Algorithm Correctness; Tarjan, 1972). *Tarjan's algorithm computes all strongly connected components of a directed graph G = (V, E) in O(|V| + |E|) time using a single depth-first search.*

*Reference.* Tarjan, R.E. (1972). "Depth-First Search and Linear Graph Algorithms." *SIAM J. Computing*, 1(2), pp. 146–160. We cite this classical result without reproducing the full proof.

The algorithm maintains a DFS stack and uses two indices per vertex — a DFS discovery index and a low-link value — to detect SCCs. When a vertex's low-link equals its discovery index, all vertices above it on the DFS stack form an SCC.

**Theorem 3.2** (SCC ⟺ Recursive Loop). *A category C belongs to an accepting SCC of the category dependency graph G if and only if C participates in a recursive parsing loop.*

*Proof.* We prove both directions.

(⟹) Suppose C ∈ S where S is an accepting SCC.

- **Case |S| > 1**: There exist distinct categories C = C₁, C₂, ..., Cₖ = C in S with edges (Cᵢ, Cᵢ₊₁) for each i. Each edge means a rule of Cᵢ contains NonTerminal(Cᵢ₊₁). Therefore, parsing C may invoke C₂, which may invoke C₃, ..., which eventually invokes C again. This is a recursive parsing loop of length k.

- **Case S = {C} with (C, C) ∈ E**: A rule of C contains NonTerminal(C). Parsing C may recursively invoke C. This is a direct (self-) recursive loop.

(⟸) Suppose C participates in a recursive parsing loop: there is a sequence C = C₁ → C₂ → ... → Cₖ → C₁ in the dependency graph. Then all of C₁, ..., Cₖ can reach each other, so they belong to the same SCC. If k > 1, the SCC has size > 1. If k = 1, the loop is C → C (self-loop). In both cases, the SCC is accepting by Definition 3.3. ∎

**Theorem 3.3** (Liveness Recovery Correctness). *The liveness multipliers (InsertToken discount 0.7, SkipToSync penalty 1.3) applied to categories in accepting SCCs maintain parsing momentum without altering the correctness of recovery. Specifically:*

*(a) The multipliers only affect the relative cost ranking of recovery actions for erroneous input; they do not change the parser's behavior on valid input.*

*(b) InsertToken at discount 0.7 is safe because inserting a synthetic token in a recursive context preserves the nesting structure: the parser continues recursive descent with the synthetic token, and subsequent valid tokens can be parsed normally.*

*(c) SkipToSync at penalty 1.3 is safe because penalizing skip in recursive contexts discourages premature loop exit: the parser prefers to stay within the recursive context and attempt insertion-based recovery.*

*Proof.*

*Part (a)*: Recovery actions are only considered when the parser encounters an unexpected token (a parse error). On valid input, no recovery is triggered, so the multipliers have no effect.

*Part (b)*: InsertToken creates a synthetic token and advances the parser as if the token were present. In a recursive context (category in accepting SCC), the parser expects a specific token to continue the recursion (e.g., an operator in an infix expression). Inserting this token allows the parser to:
1. Complete the current recursive level.
2. Continue parsing subsequent tokens, which may be valid at the current or enclosing level.
The 0.7 discount makes this action cheaper than the baseline, increasing its likelihood of being selected. The worst case is that the inserted token leads to another error, triggering another recovery step — the parser does not enter an infinite loop because each recovery step advances the input position or reduces the nesting depth.

*Part (c)*: SkipToSync abandons tokens until a synchronization point is found. In a recursive context, synchronization points are typically at the boundary of the enclosing scope (e.g., a semicolon or closing bracket). Skipping to such a point exits the recursive loop, potentially discarding many valid tokens that could have been parsed. The 1.3 penalty makes this action more expensive, deferring it in favor of less destructive alternatives. The action remains available as a last resort when insertion-based recovery fails. ∎

*Remark.* The specific values 0.7 and 1.3 were chosen empirically to produce good recovery behavior across a range of grammars. The theoretical contribution is the qualitative direction (discount insert, penalize skip in recursive contexts), not the specific constants.

## 4. Algorithm

### Algorithm 3: Tarjan's SCC on the Category Dependency Graph

```
PROCEDURE ANALYZE-CATEGORY-SCCS(all_syntax, categories)
  INPUT:  all_syntax = [(cat, label, items)]  — all grammar rules
          categories = [CategoryInfo]          — category metadata
  OUTPUT: BuchiAnalysis = {
            num_states, num_accepting, has_accepting_cycle,
            accepting_sccs: [SCC]
          }

  1. // Phase 1: Build adjacency list
     V ← {C.name : C ∈ categories}
     adj ← empty adjacency map
     FOR EACH rule (cat, label, items) IN all_syntax:
       FOR EACH item IN items:
         IF item = NonTerminal(target) THEN
           adj[cat] ← adj[cat] ∪ {target}

  2. // Phase 2: Track self-loops
     self_loop ← ∅
     FOR EACH category C:
       IF C ∈ adj[C] THEN self_loop ← self_loop ∪ {C}

  3. // Phase 3: Tarjan's algorithm
     index_counter ← 0
     stack ← []
     on_stack ← ∅
     index ← {}     // vertex → discovery index
     lowlink ← {}   // vertex → low-link value
     sccs ← []

     PROCEDURE STRONGCONNECT(v):
       index[v] ← index_counter
       lowlink[v] ← index_counter
       index_counter ← index_counter + 1
       stack.push(v)
       on_stack ← on_stack ∪ {v}

       FOR EACH w ∈ adj[v]:
         IF w ∉ index THEN           // w not yet visited
           STRONGCONNECT(w)
           lowlink[v] ← min(lowlink[v], lowlink[w])
         ELSE IF w ∈ on_stack THEN   // w is on the stack → back edge
           lowlink[v] ← min(lowlink[v], index[w])

       IF lowlink[v] = index[v] THEN // v is SCC root
         scc ← []
         REPEAT
           w ← stack.pop()
           on_stack ← on_stack \ {w}
           scc ← scc ∪ {w}
         UNTIL w = v
         sccs ← sccs ∪ {scc}

     FOR EACH v ∈ V:
       IF v ∉ index THEN STRONGCONNECT(v)

  4. // Phase 4: Classify SCCs
     accepting_sccs ← ∅
     FOR EACH scc ∈ sccs:
       IF |scc| > 1 THEN
         accepting_sccs ← accepting_sccs ∪ {scc}   // non-trivial cycle
       ELSE IF scc = {v} AND v ∈ self_loop THEN
         accepting_sccs ← accepting_sccs ∪ {scc}   // self-recursive

  5. RETURN BuchiAnalysis {
       num_states: |V|,
       num_accepting: |{v : v ∈ some accepting SCC}|,
       has_accepting_cycle: accepting_sccs ≠ ∅,
       accepting_sccs
     }

  COMPLEXITY: O(|V| + |E|) — single DFS traversal
```

## 5. Worked Example

Consider the grammar:

```
Expr ::= Atom | Expr "+" Expr | "(" Stmt ")"
Stmt ::= Expr ";" | "if" Expr "then" Stmt
Decl ::= "let" IDENT "=" Expr
```

**Category dependency graph**:

    Expr → {Atom, Expr, Stmt}
    Stmt → {Expr, Stmt}
    Decl → {Expr}

**Adjacency list** (excluding Atom which has no outgoing edges):

    Expr: [Atom, Expr, Stmt]
    Stmt: [Expr, Stmt]
    Decl: [Expr]
    Atom: []

**Self-loops**: Expr → Expr (yes), Stmt → Stmt (yes).

**Tarjan's algorithm** (starting from Expr):
1. Visit Expr (index 0), push onto stack.
2. Visit Atom (index 1), push. Atom has no successors. lowlink[Atom] = 1 = index[Atom]. Pop {Atom} as SCC₁. Singleton, no self-loop → non-accepting.
3. Back to Expr. Visit Expr — already on stack, so lowlink[Expr] = min(0, 0) = 0. Visit Stmt (index 2), push.
4. From Stmt: visit Expr — on stack, lowlink[Stmt] = min(2, 0) = 0. Visit Stmt — on stack, lowlink[Stmt] = min(0, 2) = 0.
5. Back in Stmt: lowlink[Stmt] = 0 ≠ index[Stmt] = 2, so Stmt is not an SCC root.
6. Back in Expr: lowlink[Expr] = 0 = index[Expr]. Pop from stack: {Stmt, Expr} = SCC₂. |SCC₂| = 2 > 1 → **accepting**.
7. Visit Decl (index 3), push. Visit Expr — not on stack (already popped). lowlink[Decl] = 3 = index[Decl]. Pop {Decl} as SCC₃. Singleton, no self-loop → non-accepting.

**Result**: 2 SCCs identified, 1 accepting: {Expr, Stmt}.

**Recovery consequence**:
- Expr and Stmt: `recursive_category = true`. InsertToken discount 0.7×, SkipToSync penalty 1.3×.
- Decl: `recursive_category = false`. No liveness adjustment.

## 6. Diagram

### Category Dependency Graph

```
  ┌───────┐          ┌───────┐          ┌───────┐
  │ Expr  │─────────▶│ Stmt  │          │ Decl  │
  │       │◀─────────│       │          │       │
  └───┬───┘          └───┬───┘          └───┬───┘
      │  ↺               │  ↺               │
      │  (self-loop)      │  (self-loop)      │
      │                   │                   │
      │         ┌───────┐ │                   │
      └────────▶│ Atom  │ │                   │
                │       │ │                   │
                └───────┘ │                   │
                          │                   │
      ┌───────────────────┘                   │
      │                                       │
      ▼                                       ▼
  Expr ◀──────────────────────────────── Decl
```

### SCC Decomposition

```
  ┌─────────────────────────────────┐
  │  SCC₂ (accepting)               │
  │  ┌───────┐      ┌───────┐      │
  │  │ Expr  │◀────▶│ Stmt  │      │     ┌───────┐     ┌───────┐
  │  │  ↺    │      │  ↺    │      │     │ Atom  │     │ Decl  │
  │  └───────┘      └───────┘      │     │ SCC₁  │     │ SCC₃  │
  │                                │     │(triv.)│     │(triv.)│
  │  recursive_category = true     │     └───────┘     └───────┘
  │  InsertToken: 0.7×             │
  │  SkipToSync:  1.3×             │     recursive_category = false
  └─────────────────────────────────┘     multipliers = 1.0×
```

### Recovery Cost Landscape

```
                    Non-recursive          Recursive (in SCC)
                    ─────────────          ──────────────────
  InsertToken:      base × 1.0            base × 0.7  (cheaper)
  SkipToSync:       base × 1.0            base × 1.3  (more expensive)
  DeleteToken:      base × 1.0            base × 1.0  (unchanged)

  Effect: In recursive contexts, insertion is preferred over skipping.

  Cost comparison (base = 1.0):
  ┌──────────────┬─────────────┬──────────────┐
  │ Action       │ Non-recursive│ Recursive   │
  ├──────────────┼─────────────┼──────────────┤
  │ InsertToken  │    1.0      │    0.7       │
  │ SkipToSync   │    1.0      │    1.3       │
  │ DeleteToken  │    1.0      │    1.0       │
  │ Substitute   │    1.0      │    1.0       │
  └──────────────┴─────────────┴──────────────┘
```

## 7. Implementation References

- **`analyze_from_bundle()`** — `buchi.rs:1025`: Entry point for SCC analysis. Builds the category dependency graph, runs Tarjan's algorithm, filters accepting SCCs.
- **`BuchiAnalysis`** — `buchi.rs`: Result struct with `num_states`, `num_accepting`, `has_accepting_cycle`, `accepting_sccs`.
- **`RecoveryWfst::set_recursive_category()`** — `recovery.rs:588`: Wires SCC membership into the recovery WFST.
- **`RecoveryWfst::is_recursive_category()`** — `recovery.rs:594`: Query method for SCC membership.
- **Liveness skip penalty** — `recovery.rs:2168`: `let liveness_skip_mult = if self.recursive_category { 1.3 } else { 1.0 };`
- **Liveness insert discount** — `recovery.rs:2231`: `let liveness_insert_mult = if self.recursive_category { 0.7 } else { 1.0 };`

## 8. Cross-References

- `theory/disambiguation/vpa-nesting-recovery.md` — VPA nesting ceiling (complementary depth-based mechanism)
- `theory/disambiguation/information-theoretic-dispatch.md` — Entropy-based analysis (orthogonal)
- `theory/omega/weighted-omega.md` — Buchi automata theory for omega-regular properties
- `docs/diagnostics/buchi/O01.md` — O01 lint: accepting cycle detected
- `docs/diagnostics/buchi/O02.md` — O02 lint: non-trivial mutual recursion

## 9. Bibliography

1. Tarjan, R.E. (1972). "Depth-First Search and Linear Graph Algorithms." *SIAM J. Computing*, 1(2), pp. 146–160.

2. Buchi, J.R. (1962). "On a Decision Method in Restricted Second Order Arithmetic." *International Congress on Logic, Method, and Philosophy of Science*, pp. 1–11. Stanford University Press.

3. Couvreur, J.-M. (1999). "On-the-Fly Verification of Linear Temporal Logic." *FM'99: Formal Methods*, LNCS 1708, pp. 253–271. Springer.

4. Alur, R. & Madhusudan, P. (2004). "Visibly Pushdown Languages." *STOC*, pp. 202–211. ACM.
