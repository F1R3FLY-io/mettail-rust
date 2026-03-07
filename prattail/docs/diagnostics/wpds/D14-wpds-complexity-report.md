# D14: wpds-complexity-report

**Severity:** Info
**Category:** WPDS

## Description

Emits a summary of WPDS analysis complexity metrics: stack alphabet size (|Gamma|), PDS rule count (|Delta|), number of strongly connected components, call graph edge count, reachable vs total categories, cycle count, recursive category count, and depth bounds. This diagnostic provides grammar authors with visibility into the WPDS analysis layer's scope.

## Trigger Conditions

A D14 diagnostic fires when WPDS analysis completes (i.e., the grammar has >=2 categories and the G25 optimization gate is enabled).

## Example

### Grammar

```
language! {
    name: ComplexLang;
    primary: Expr;

    category Expr {
        native_type: Integer;
        Num      = <int>;
        Add      = Expr "+" Expr;
        LetExpr  = "let" Decl "in" Expr;
        TypeCast = "(" Type ")" Expr;
    }

    category Decl {
        VarDecl  = "var" Type;
        FunDecl  = "fun" "(" Type ")" Expr;   // Decl → Expr (mutual recursion)
    }

    category Type {
        IntType  = "int";
        ArrType  = Type "[" "]";              // left recursion within Type
        FunType  = Type "->" Type;
    }

    category Pattern {
        PatVar   = IDENT;                     // orphan: no category calls Pattern
    }
}
```

### Output

```
info[D14]: WPDS analysis: |Γ|=8, |Δ|=12, 2 SCCs, 5 call edges, 3/4 reachable
           categories, 1 cycle, 2 recursive; recursive SCCs: {Expr, Decl};
           max_depth: Type=1, Decl=2
```

### Field-by-Field Interpretation

| Field | Value | Meaning |
|-------|-------|---------|
| `|Γ|=8` | 8 stack symbols | 4 categories × 2 symbols each (entry + return) |
| `|Δ|=12` | 12 PDS rules | Push + Replace + Pop rules across all cross-category references |
| `2 SCCs` | 2 strongly connected components | Tarjan decomposition found 2 nontrivial SCCs |
| `5 call edges` | 5 inter-category calls | Edges in the G33 call graph |
| `3/4 reachable` | 3 of 4 categories reachable | `Pattern` is unreachable from root `Expr` |
| `1 cycle` | 1 classified cycle | `Expr ↔ Decl` mutual recursion |
| `2 recursive` | 2 recursive categories | Categories in nontrivial SCCs |
| `max_depth` | `Type=1, Decl=2` | Minimum BFS depth from primary to each bounded category |

## Resolution

This is an informational diagnostic. No action required. Use it to understand the grammar's inter-category complexity:

- **High |Δ|** relative to category count suggests complex cross-category interactions.
- **Nontrivial SCCs** identify mutual recursion that increases WPDS saturation cost.
- **Unreachable categories** (reachable < total) indicate orphan categories (see W13).
- **Bounded max_depth** values feed RT-01 frame pool pre-sizing (`Vec::with_capacity(max_depth + 1)`).

## Hint Explanation

No hint is emitted for Info-level diagnostics.

## Related Lints

- [P05](../performance/P05-wpds-pipeline-cost.md) -- WPDS wall-clock timing (complements D14 with execution cost).
- [D05](../decision-tree/D05-decision-tree-summary.md) -- Decision tree summary (analogous Info diagnostic for the PathMap layer).
