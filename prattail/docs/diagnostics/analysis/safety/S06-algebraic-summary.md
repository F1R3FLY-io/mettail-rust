# S06: algebraic-summary

**Severity:** Note
**Category:** analysis/safety
**Feature Gate:** always-on

## Description

Reports the structural summary of Tarjan's path expression analysis applied to
the grammar's inter-procedural call graph. The analysis decomposes the call graph
into strongly connected components (SCCs) and computes a regular path expression
for each SCC. These path expressions encode the set of all call/return sequences
within each SCC as a regular language, enabling algebraic summarization of
inter-procedural data flow.

The motivation for reporting this summary is that the SCC structure of the call
graph is a fundamental property of the grammar's inter-procedural architecture.
The number of SCCs indicates how many groups of mutually recursive categories
exist, while the number of path expressions reflects the combinatorial complexity
of call patterns within those groups.

### Tarjan's path expression algorithm

Given a directed graph G = (V, E) representing the inter-category call graph
(categories are vertices, cross-category calls are edges), Tarjan's algorithm
proceeds in three steps:

1. **SCC decomposition.** Compute the strongly connected components of G using
   Tarjan's depth-first search algorithm. Each SCC is a maximal set of mutually
   reachable vertices.

2. **DAG reduction.** Collapse each SCC into a single node, yielding a DAG
   (directed acyclic graph) of SCCs.

3. **Path expression computation.** For each SCC with k vertices and m edges,
   compute a regular expression over the semiring of transition weights that
   represents all paths within the SCC. This uses the star operation (Kleene
   closure) for cycles.

The path expression for an SCC with vertices {v_1, ..., v_k} has the form:

  E(v_i, v_j) = sum over all paths p from v_i to v_j of product of edge weights along p

which is computed efficiently using semiring operations:

  E = (I oplus A oplus A^2 oplus ...)* = A*

where A is the adjacency matrix of the SCC weighted by transition weights, and
A* is the Kleene closure (star semiring closure).

### SCC and path expression relationship

```
  Inter-category call graph:

    ┌──────┐      ┌──────┐      ┌──────┐
    │ Proc │─────>│ Expr │─────>│ Name │
    └──┬───┘      └──┬───┘      └──────┘
       │             │
       │             │ (mutual recursion)
       v             v
    ┌──────┐      ┌──────┐
    │ Stmt │<─────│ Type │
    └──────┘      └──────┘

  SCC decomposition:

    SCC_0: {Proc, Stmt}    -- mutually recursive
    SCC_1: {Expr, Type}    -- mutually recursive
    SCC_2: {Name}          -- singleton (no self-loop)

  DAG of SCCs:

    SCC_0 ──> SCC_1 ──> SCC_2

  Path expressions:
    E(SCC_0): (Proc -> Stmt | Stmt -> Proc)*
    E(SCC_1): (Expr -> Type | Type -> Expr)*
    E(SCC_2): epsilon (trivial)
```

The S06 message reports:
- The number of SCCs (3 in this example).
- The number of path expressions computed (one per non-trivial SCC, so 2
  in this example if singleton SCCs are excluded from the count, or 3 if all
  SCCs are counted).

## Trigger Conditions

A note is emitted when **all** of the following conditions hold:

1. The pipeline's algebraic analysis module (`algebraic.rs`) has been executed,
   producing an `AlgebraicSummary`.

The lint is silent when:
- No `AlgebraicSummary` is available (analysis was not run).

The diagnostic always fires when the analysis result exists, even for trivial
grammars (e.g., 1 SCC, 0 non-trivial expressions), providing a consistent
record of the analysis outcome.

## Example

### Grammar

```
language! {
    name: MiniLang;
    primary: Proc;

    category Proc {
        Call    = "call" Name "(" Expr ")";
        Assign  = Name ":=" Expr;
        Seq     = Proc ";" Proc;
        IfElse  = "if" Expr "then" Proc "else" Proc;
    }

    category Expr {
        native_type: Integer;
        IntLit = <int>;
        Add    = Expr "+" Expr;
        Var    = Name;
        FnApp  = Name "(" Expr ")";
    }

    category Name {
        Ident = <ident>;
    }
}
```

The call graph has edges Proc -> Expr, Proc -> Name, Expr -> Name. Tarjan's
algorithm identifies 3 SCCs (each category is its own SCC since there is no
mutual recursion), and computes path expressions for each.

### Output

```
note[S06] (MiniLang): Tarjan path expression summary: 3 SCC(s), 2 expression(s)
```

## Resolution

S06 is informational. The SCC count and path expression count characterize the
grammar's inter-procedural complexity:

- **1 SCC, 0 expressions:** The grammar has a single category or no
  cross-category calls. Inter-procedural analysis is trivially precise.

- **Many SCCs, few expressions:** The grammar has many categories but they
  form mostly independent groups. Analysis scales well.

- **Few SCCs, many expressions:** Highly recursive grammar structure with
  complex call patterns. Analysis may be expensive; consider whether all
  mutual recursion is necessary.

- **Many SCCs, many expressions:** Complex grammar with both breadth and
  depth in its inter-procedural structure. Consider modularizing the grammar.

The SCC structure also directly impacts:
- [S03](S03-cegar-refinement.md): CEGAR refinement depth correlates with SCC complexity.
- [S05](S05-ara-invariant.md): ARA recurrence dimension scales with SCC sizes.
- [S01](S01-safety-violation.md): Prestar saturation cost depends on the path expression structure.

## Hint Explanation

S06 does not include a hint, as it is purely informational. The SCC count and
expression count provide a compact summary of the call graph's algebraic
structure.

## Related Lints

- [S01](S01-safety-violation.md) -- Safety verification uses the call graph structure summarized by S06
- [S03](S03-cegar-refinement.md) -- CEGAR refinement depth is influenced by SCC complexity
- [S05](S05-ara-invariant.md) -- ARA invariant discovery uses the SCC decomposition for recurrence extraction
- [D14](../../wpds/D14-wpds-complexity-report.md) -- WPDS complexity report includes SCC counts from the same call graph analysis
