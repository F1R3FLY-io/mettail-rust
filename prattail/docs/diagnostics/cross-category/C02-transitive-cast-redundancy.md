# C02: transitive-cast-redundancy

**Severity:** Note
**Category:** Cross-Category

## Description

Detects direct cast rules that are redundant because a transitive path of length >= 2 already provides the same coercion. For example, if cast rules define `Int -> Expr` and `Expr -> Proc`, then the transitive path `Int -> Expr -> Proc` already allows `Int` values to reach `Proc` contexts. A direct cast rule `Int -> Proc` is therefore redundant -- it duplicates a coercion that the parser would perform automatically by chaining the two existing casts.

This is a note-level diagnostic, not a warning, because the direct rule may be intentional: it avoids the runtime overhead of an intermediate `Box::new()` wrapper at each cast level, and it makes the grammar's coercion semantics more explicit to readers. The lint surfaces the redundancy so the grammar author can make an informed decision.

The detection algorithm works in two phases:

1. **Floyd-Warshall transitive closure.** Build the cast adjacency set from all cast rules, then compute the full transitive reachability matrix using the standard O(V^3) Floyd-Warshall algorithm over the category set.
2. **Indirect path check.** For each direct cast rule `src -> dst`, check whether there exists any intermediate category `mid` such that `src -> mid` is a direct edge AND `mid -> dst` is transitively reachable. If so, the path `src -> mid -> ... -> dst` has length >= 2, making the direct rule redundant.

## Trigger Conditions

A note is emitted when **all** of the following hold:

1. A cast rule with label `L` defines a direct edge `src -> dst`.
2. There exists at least one intermediate category `mid` (where `mid != dst`) such that:
   - `src -> mid` is a direct cast edge (in the adjacency set), AND
   - `mid -> dst` is reachable in the transitive closure (i.e., there is a path from `mid` to `dst` through zero or more intermediate categories).
3. The combination of conditions (a) and (b) means a path of length >= 2 exists from `src` to `dst`.

The lint does **not** fire if the only path from `src` to `dst` is the direct edge itself.

## Example

### Grammar

```
language! {
    name: TypeHierarchy,
    types {
        ![i32] as Int
        ![f64] as Float
        ![String] as Str
        ![()] as Proc
    },
    terms {
        // Arithmetic
        NumLit   . |- @integer : Int;
        FloatLit . |- @float : Float;
        StrLit   . |- @string : Str;
        Add      . a:Int, b:Int |- a "+" b : Int ![a + b] fold;

        // Cast chain: Int -> Float -> Proc (length 2)
        CastIntToFloat  . a:Int   |- a : Float ![a as f64] step;
        CastFloatToProc . a:Float |- a : Proc step;

        // Direct cast Int -> Proc (redundant -- Int -> Float -> Proc exists)
        CastIntToProc . a:Int |- a : Proc step;

        // String cast (independent, not redundant)
        CastStrToProc . a:Str |- a : Proc step;

        // Process operations
        POutput . a:Str |- "stdout" "!" "(" a ")" : Proc step;
    },
}
```

In this grammar, `CastIntToFloat` creates edge `Int -> Float`, and `CastFloatToProc` creates edge `Float -> Proc`. The transitive closure includes `Int -> Proc` via `Int -> Float -> Proc`. The direct rule `CastIntToProc` is therefore redundant with the transitive path.

### Output

```
note[C02]: direct cast `Int` -> `Proc` (rule `CastIntToProc`) is redundant — a transitive path already exists
  = hint: the transitive path handles this cast — the direct rule may be intentional for performance or explicitness
```

## Resolution

1. **Remove the direct cast** if the transitive path is sufficient and performance is not a concern:

   ```
   // Remove: CastIntToProc . a:Int |- a : Proc step;
   // The path Int -> Float -> Proc handles this coercion automatically.
   ```

2. **Keep the direct cast** if the intermediate cast introduces unwanted semantic overhead. Each level in a cast chain adds a `Box::new()` wrapper in the generated AST. For frequently-used coercions, a direct cast avoids the intermediate allocation:

   ```
   // Keep for performance: bypasses the Float intermediate wrapper
   CastIntToProc . a:Int |- a : Proc step;
   ```

3. **Keep the direct cast with a comment** to document the intentional redundancy for future grammar maintainers:

   ```
   // Direct cast for performance (bypasses Int -> Float -> Proc chain)
   CastIntToProc . a:Int |- a : Proc step;
   ```

## Hint Explanation

The hint "the transitive path handles this cast -- the direct rule may be intentional for performance or explicitness" acknowledges that redundancy is not necessarily a defect. The transitive closure guarantees that the coercion is already available through chained casts, but the direct rule serves two legitimate purposes:

- **Performance.** Each cast level in the chain wraps the value in a `Box::new()` allocation for the intermediate category's AST enum variant. A direct cast produces only one wrapper instead of N wrappers for an N-level chain. For hot paths (e.g., integer literals in a process calculus where `Int -> Proc` is extremely common), the allocation savings can be significant.

- **Explicitness.** A direct cast rule makes the grammar's intent clear: `Int` values should be directly usable in `Proc` contexts without the reader needing to trace through intermediate categories to discover that the coercion is available.

The Floyd-Warshall algorithm ensures that all transitive paths are considered, including paths through multiple intermediates (e.g., `A -> B -> C -> D` makes a direct `A -> D` redundant). The lint does not recommend a specific resolution because the correct choice depends on the grammar's performance profile and documentation conventions.

## Related Lints

- [C01](C01-cast-cycle.md) -- cycles in the cast graph are a more severe problem (Error) that must be resolved before transitive redundancy analysis is meaningful; C01 always runs before C02
- [G08](../grammar/G08-missing-cast-to-root.md) -- a category with no cast path to the primary category may indicate that a needed cast rule was accidentally removed during redundancy cleanup
