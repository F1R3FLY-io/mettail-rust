# C01: cast-cycle

**Severity:** Error
**Category:** Cross-Category

## Description

Detects cycles in the cast rule directed graph. A cast rule defines an implicit type coercion between categories (e.g., `Int` can be cast to `Proc`). When cast rules form a cycle (e.g., `Int -> Proc -> Int`), the generated parser enters infinite recursion: `parse_Proc` calls `parse_Int` via a cast, which calls `parse_Proc` via the reverse cast, and so on, without consuming any tokens. This is a correctness bug that must be fixed before the grammar can compile.

The detection algorithm performs a depth-first search over the cast DAG using three-color marking (White/Gray/Black):

1. **White** -- the category has not yet been visited.
2. **Gray** -- the category is currently on the DFS stack (i.e., it is an ancestor of the node being explored).
3. **Black** -- the category and all its descendants have been fully explored.

When the DFS encounters a Gray node, it has found a back edge, which is the necessary and sufficient condition for a cycle in a directed graph. The cycle path is extracted by slicing the DFS stack from the first occurrence of the Gray node to the current position and appending the Gray node again to close the cycle string.

## Trigger Conditions

An error is emitted when **all** of the following hold:

1. The grammar defines at least two cast rules whose `source_category` and `target_category` fields form a directed graph.
2. A DFS traversal from any unvisited (White) category encounters a back edge -- that is, a neighbor whose color is Gray (currently on the DFS stack).
3. The cycle path is extracted as the subsequence of the DFS stack from the cycle entry point back to itself (e.g., `Int -> Proc -> Int`).

Multiple cycles are reported independently if the graph contains more than one strongly connected component with cycles.

## Example

### Grammar

```
language! {
    name: CyclicLang,
    types {
        ![i32] as Int
        ![String] as Str
        ![()] as Proc
    },
    terms {
        // Arithmetic
        NumLit  . |- @integer : Int;
        Add     . a:Int, b:Int |- a "+" b : Int ![a + b] fold;

        // String operations
        StrLit  . |- @string : Str;
        Concat  . a:Str, b:Str |- a "++" b : Str ![[a, b].concat()] fold;

        // Bidirectional casts create a cycle: Int -> Proc -> Int
        CastIntToProc . a:Int |- a : Proc step;
        CastProcToInt . a:Proc |- a : Int step;

        // Process operations
        POutput . a:Str |- "stdout" "!" "(" a ")" : Proc step;
    },
}
```

In this grammar, `CastIntToProc` creates an edge `Int -> Proc` and `CastProcToInt` creates an edge `Proc -> Int`, forming the cycle `Int -> Proc -> Int`. During parsing, `parse_Proc` would attempt to parse its cast operand as `Int`, which would then attempt to parse its cast operand as `Proc`, recursing infinitely.

### Output

```
error[C01]: cast cycle detected: Int -> Proc -> Int
  = hint: break the cycle by removing one cast direction
```

## Resolution

1. **Remove one direction of the cast.** Determine which direction is semantically required. If `Int` values should be usable in `Proc` contexts but not vice versa, remove `CastProcToInt`:

   ```
   // Keep only the upward cast:
   CastIntToProc . a:Int |- a : Proc step;
   // Remove: CastProcToInt . a:Proc |- a : Int step;
   ```

2. **Introduce an explicit conversion rule instead of a cast.** If both directions are needed, replace one cast with a named operator that the user invokes explicitly, breaking the implicit cycle:

   ```
   CastIntToProc . a:Int |- a : Proc step;
   // Explicit conversion (not a cast -- requires "int(" prefix):
   ExplicitToInt . a:Proc |- "int" "(" a ")" : Int step;
   ```

3. **Introduce an intermediate category.** If the relationship is complex, add a new category that acts as an explicit bridge:

   ```
   CastIntToExpr . a:Int |- a : Expr step;
   CastProcToExpr . a:Proc |- a : Expr step;
   // No cast from Expr back to Int or Proc -- DAG is maintained.
   ```

## Hint Explanation

The hint "break the cycle by removing one cast direction" identifies the minimal fix: in a cycle of length N, removing any single edge breaks the cycle. Cast rules generate implicit coercion code in the parser, so a cycle means two (or more) categories mutually coerce to each other without any token consumption to advance the parser position. The DFS algorithm guarantees that every reported cycle is minimal with respect to the traversal order, though the grammar may contain additional cycles that are reported in subsequent DFS iterations from other unvisited roots.

Since cast rules are implicit (they fire automatically when a category mismatch is detected during dispatch), the parser has no mechanism to decide which direction to apply first. This makes cycles fundamentally ambiguous at the grammar level, not just at the implementation level. The resolution must be made by the grammar author based on the intended type hierarchy.

## Related Lints

- [G08](../grammar/G08-missing-cast-to-root.md) -- a category with no cast path to the root/primary category is the opposite problem: disconnection rather than over-connection
- [C02](C02-transitive-cast-redundancy.md) -- after removing a cast to break a cycle, the remaining path may create a transitive redundancy with other direct casts
