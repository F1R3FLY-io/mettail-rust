# X04: composition-cast-chain-break

**Severity:** Error
**Category:** Composition
**Feature Gate:** (none -- always active when composition lints run)

## Description

Detects cast chains that exist in a source grammar but are broken after
composition. A **cast chain** is a directed path A -> B -> C -> ... in the
cast rule graph, where each edge represents a cast rule that converts a value
from one category to another. If the composition removes or overrides an
intermediate cast rule, the chain breaks and values can no longer flow along
the original path.

The lint computes the transitive reachability closure for each source
grammar's cast graph and for the merged grammar's cast graph, then checks
that every pair (src, dst) reachable in either source is still reachable in
the merged grammar:

    reachable_A  = transitive_closure(cast_graph_A)
    reachable_B  = transitive_closure(cast_graph_B)
    reachable_M  = transitive_closure(cast_graph_merged)

    broken = (reachable_A ∪ reachable_B) \ reachable_M

Each pair in `broken` represents a cast path that existed before composition
but no longer exists after.

```
  Grammar A:             Merged:
  ┌───┐    ┌───┐    ┌───┐     ┌───┐    ┌───┐    ┌───┐
  │ A │ ──→│ B │ ──→│ C │     │ A │ ──→│ B │    │ C │
  └───┘    └───┘    └───┘     └───┘    └───┘    └───┘
     reachable: (A,B) (A,C) (B,C)        B->C cast lost!
                                          broken: (A,C) (B,C)
```

This lint has **Error** severity because a broken cast chain is a correctness
problem: code that relied on implicit type coercion through the chain will
fail to compile or produce type errors.

## Trigger Conditions

All of the following must hold:

- Two grammars A and B are composed via the composition lint framework.
- A `CompositionLintContext` is provided with rule information for both
  source grammars (including `is_cast` flags on rules).
- The base `LintContext` contains the merged grammar's cast rules.
- At least one (src, dst) pair is reachable via cast chains in a source
  grammar but not reachable in the merged grammar.

One diagnostic is emitted per broken (src, dst) pair.

## Example

### Grammar

```rust
// Grammar A: cast chain Int -> Float -> String
language! {
    name: TypesA,
    types {
        ![i32] as Int
        ![f64] as Float
        ![String] as Str
    },
    terms {
        IntToFloat . n:Int |- n : Float  ![n as f64] step;
        FloatToStr . f:Float |- f : Str  ![f.to_string()] step;
    },
}

// Grammar B: overrides Float -> Str with a different rule
// but accidentally uses a different category name "Text" instead of "Str"
language! {
    name: TypesB,
    types {
        ![f64] as Float
        ![String] as Text
    },
    terms {
        FloatToText . f:Float |- f : Text ![f.to_string()] step;
    },
}

// After composition, the Float -> Str cast is lost (replaced by Float -> Text),
// breaking the chain Int -> Float -> Str.
```

### Output

```
error[X04] (MergedTypes): cast chain `Int` -> `Str` from grammar A is broken after composition
  = hint: ensure all intermediate cast rules are preserved in the composed grammar, or add explicit casts to restore the chain

error[X04] (MergedTypes): cast chain `Float` -> `Str` from grammar A is broken after composition
  = hint: ensure all intermediate cast rules are preserved in the composed grammar, or add explicit casts to restore the chain
```

## Resolution

1. **Restore the intermediate cast.** Add the missing cast rule to the
   composed grammar to reconnect the chain:

   ```
   FloatToStr . f:Float |- f : Str ![f.to_string()] step;
   ```

2. **Add an explicit bridge cast.** If the intermediate category was
   intentionally removed, add a direct cast from source to destination:

   ```
   IntToStr . n:Int |- n : Str ![n.to_string()] step;
   ```

3. **Align category names.** If the break is caused by a category name
   mismatch (e.g., `Str` vs `Text`), unify the names so the cast edges
   connect properly.

4. **Accept the break.** If the cast chain is intentionally removed in the
   composed grammar (e.g., to restrict implicit coercions), suppress the
   error by removing the source-grammar cast rules that created the
   expectation.

## Hint Explanation

> ensure all intermediate cast rules are preserved in the composed grammar,
> or add explicit casts to restore the chain

The hint identifies two approaches: (1) preserve all intermediate cast rules
from the source grammars in the composed grammar, which maintains the
original reachability paths, or (2) add new direct cast rules that bypass the
removed intermediate, restoring reachability through a shorter path. The key
insight is that cast chain reachability is transitive -- if any intermediate
link is removed, all paths through that link break.

## Related Lints

- [X03](X03-composition-dead-rule-creation.md) -- detects rules that become
  dead after composition; a cast rule becoming dead can cause X04 to fire
- [C01](../cross-category/C01-cast-cycle.md) -- detects cycles in the cast
  graph (a different structural problem in the cast rule system)
- [G08](../grammar/G08-missing-cast-to-root.md) -- detects categories with
  no cast path to the root category (related reachability concern in a
  single grammar)
