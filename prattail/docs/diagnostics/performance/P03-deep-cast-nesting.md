# P03: deep-cast-nesting

**Severity:** Note
**Category:** Performance

## Description

Detects cast chains whose longest path exceeds a depth of 3. Each level in a cast chain adds a `Box::new()` wrapper in the generated AST: when a value of category `A` is cast to category `B`, the generated code wraps the `A` value in `B`'s AST enum variant, which requires a heap allocation (`Box::new()`) for the inner value. A chain `A -> B -> C -> D -> E` (depth 4) produces 4 nested `Box::new()` calls for a single value traversing the full chain, each allocating on the heap and adding pointer indirection.

The detection algorithm uses dynamic programming over the cast DAG to find the longest path:

1. **Build the cast adjacency list** from all cast rules (directed edges from `source_category` to `target_category`).
2. **Compute longest path via DP with memoization.** For each category, recursively compute the maximum depth reachable through cast edges, caching results to avoid redundant computation.
3. **Defensive cycle guard.** Although C01 (cast-cycle) runs before P03 and would report any cycles, the DP function includes a visited-set guard to prevent infinite recursion in case a cycle was not caught.

The lint reports the maximum depth and all starting categories that achieve that depth, enabling the grammar author to identify which chains to optimize.

## Trigger Conditions

A note is emitted when:

1. The maximum depth of any path in the cast DAG exceeds 3 (`max_depth > 3`).
2. The depth is computed as the number of edges in the longest path (not the number of nodes). A chain `A -> B -> C -> D` has depth 3; `A -> B -> C -> D -> E` has depth 4.

The diagnostic lists all categories whose longest outgoing path equals `max_depth`, sorted by the order they appear in the category list.

## Example

### Grammar

```
language! {
    name: DeepHierarchy,
    types {
        ![i32] as Int
        ![f64] as Float
        ![String] as Str
        ![bool] as Bool
        ![()] as Proc
    },
    terms {
        // Leaf literals
        NumLit   . |- @integer : Int;
        FloatLit . |- @float : Float;
        StrLit   . |- @string : Str;
        BTrue    . |- "true" : Bool;
        BFalse   . |- "false" : Bool;

        // Arithmetic
        Add . a:Int, b:Int |- a "+" b : Int ![a + b] fold;

        // Cast chain: Int -> Float -> Str -> Bool -> Proc (depth 4)
        CastIntToFloat  . a:Int   |- a : Float ![a as f64] step;
        CastFloatToStr  . a:Float |- a : Str ![a.to_string()] step;
        CastStrToBool   . a:Str   |- a : Bool ![!a.is_empty()] step;
        CastBoolToProc  . a:Bool  |- a : Proc step;

        // Process operations
        POutput . a:Str |- "stdout" "!" "(" a ")" : Proc step;
    },
}
```

In this grammar, the cast chain is:
```
Int -> Float -> Str -> Bool -> Proc
```

The longest path is 4 edges (starting from `Int`). When an `Int` value is used in a `Proc` context, the generated parser applies 4 successive casts, each wrapping the previous result in a `Box::new()`:

```rust
Proc::CastBoolToProc(Box::new(
    Bool::CastStrToBool(Box::new(
        Str::CastFloatToStr(Box::new(
            Float::CastIntToFloat(Box::new(
                Int::NumLit(42)
            ))
        ))
    ))
))
```

### Output

```
note[P03]: cast chain depth is 4 (starting from [Int]) — each level adds Box::new() wrapper overhead
  = hint: consider adding direct cast rules to bypass intermediate categories
```

## Resolution

1. **Add direct cast rules to bypass intermediates.** If `Int -> Proc` is a common coercion, add a direct cast that skips the chain:

   ```
   // Direct cast bypasses Float -> Str -> Bool intermediate wrappers
   CastIntToProc . a:Int |- a : Proc step;
   ```

   This reduces the depth to 1 for the `Int -> Proc` path. Note that C02 (transitive-cast-redundancy) will fire a note for the direct cast, which is expected and intentional.

2. **Restructure the type hierarchy.** If the deep chain reflects an overly fine-grained type hierarchy, consider whether intermediate categories are necessary:

   ```
   // Before: Int -> Float -> Str -> Bool -> Proc (depth 4)
   // After: Int -> Proc, Float -> Proc, Str -> Proc, Bool -> Proc (depth 1 each)
   CastIntToProc   . a:Int   |- a : Proc step;
   CastFloatToProc . a:Float |- a : Proc step;
   CastStrToProc   . a:Str   |- a : Proc step;
   CastBoolToProc  . a:Bool  |- a : Proc step;
   ```

   This flattens the hierarchy to a star topology with `Proc` at the center, eliminating deep nesting entirely.

3. **Accept the depth** if the type hierarchy is semantically meaningful and the cast chain is rarely traversed end-to-end. In practice, most values only traverse 1-2 levels of the chain (e.g., `Int -> Float` is far more common than `Int -> Float -> Str -> Bool -> Proc`). The overhead of deep nesting is proportional to the chain length actually traversed, not the maximum possible depth.

## Hint Explanation

The hint "consider adding direct cast rules to bypass intermediate categories" provides the most targeted fix: adding a direct cast rule `A -> Z` alongside the existing chain `A -> B -> ... -> Z` reduces the traversal cost from O(chain_length) allocations to O(1). Each `Box::new()` call in the cast chain allocates on the heap, and the resulting AST node carries pointer indirection through each intermediate wrapper. For hot paths (e.g., integer literals in a process calculus), this overhead is measurable in both allocation count and cache miss rate.

The DP algorithm computes exact depths by traversing the DAG bottom-up (leaf categories have depth 0, and each category's depth is 1 + max(child depths)). Memoization ensures O(V + E) time complexity where V is the number of categories and E is the number of cast edges. The defensive cycle guard uses a visited set that is added-to before recursion and removed-from after, preventing infinite recursion in the presence of cycles (though C01 should have caught these earlier in the lint pipeline).

Multiple starting categories may share the same maximum depth if the DAG has multiple roots feeding into the same deep chain. The diagnostic lists all such roots to help the grammar author identify all entry points that produce the deepest nesting.

## Related Lints

- [C01](../cross-category/C01-cast-cycle.md) -- cycles in the cast graph are detected before depth analysis; C01 errors must be resolved first because cycles produce infinite depth
- [C02](../cross-category/C02-transitive-cast-redundancy.md) -- adding direct casts to bypass deep chains (the recommended resolution) will trigger C02 notes for the newly-redundant direct rules; this is expected and intentional
