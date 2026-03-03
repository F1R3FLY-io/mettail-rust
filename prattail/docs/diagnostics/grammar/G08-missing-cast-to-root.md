# G08: missing-cast-to-root

**Severity:** Warning
**Category:** Grammar Structure

## Description

Detects non-primary categories that have no path to the primary (root) category via
cast rules or cross-category rules. In PraTTaIL, the primary category is the
entry point for parsing: its `parse()` method is what top-level callers invoke. If a
secondary category has no cast path to the primary, then values produced by that
category can never appear in a top-level parse result unless they are explicitly
referenced by a rule in the primary category.

The lint performs a depth-first search (DFS) from each non-primary category through
the directed graph formed by cast and cross-category rule edges
(`source_category -> target_category`). If the DFS cannot reach the primary
category, the lint fires.

A missing cast path often indicates either:

- A category that was declared but never integrated into the grammar's type hierarchy.
- A missing intermediate cast rule that should bridge two categories.
- An intentional auxiliary category that is only used internally (in which case the
  warning can be noted and ignored).

## Trigger Conditions

The lint fires when **all** of the following conditions hold:

1. The grammar has a primary category (the first category declared in `types { ... }`).
2. A non-primary category `C` exists in the grammar.
3. A DFS from `C` through the directed edge set `{ (source, target) | cast_rule(source, target) } UNION { (source, result) | cross_category_rule(source, result) }` does **not** reach the primary category.

The directed graph includes both cast rules (where `target_category` wraps
`source_category`) and cross-category rules (where `result_category` receives values
from `source_category`). The DFS follows edges in the forward direction
(`source -> target`) because cast rules transport values *from* source *into* target.

## Example

### Grammar

```
language! {
    name: TypedCalc,
    types {
        ![i32] as Proc
        ![i32] as Int
        ![bool] as Bool
        ![f64] as Float
    },
    terms {
        // Int rules
        AddInt . a:Int, b:Int |- a "+" b : Int ![a + b] fold;
        SubInt . a:Int, b:Int |- a "-" b : Int ![a - b] fold;

        // Bool rules
        EqInt  . a:Int, b:Int |- a "==" b : Bool ![a == b] step;
        Not    . a:Bool       |- "not" a  : Bool ![!a]     step;

        // Cast: Int -> Proc (so Int values are usable at top level)
        IntToProc . a:Int |- a : Proc ![a] step;

        // Cast: Bool -> Proc
        BoolToProc . a:Bool |- a : Proc ![if a { 1 } else { 0 }] step;

        // Float rules -- but NO cast to Proc, Int, or Bool
        AddFloat . a:Float, b:Float |- a "+." b : Float ![a + b] fold;
        MulFloat . a:Float, b:Float |- a "*." b : Float ![a * b] fold;
    }
}
```

Here, `Int` casts to `Proc` (primary) and `Bool` casts to `Proc`, but `Float` has
no cast path to any other category. Float values can never appear in a top-level
parse result.

### Output

```
warning[G08]: no cast path from category `Float` to primary category `Proc`
  = in category `Float`
  = hint: add a cast rule from `Float` to `Proc` or an intermediate category
```

## Resolution

To resolve this warning, add one or more cast rules that connect the isolated
category to the primary category (directly or transitively):

1. **Direct cast to primary.** Add a rule that wraps the isolated category's values
   into the primary category:

   ```
   FloatToProc . a:Float |- a : Proc
       ![a.round() as i32] step;
   ```

2. **Transitive cast via intermediate.** If a direct cast does not make semantic
   sense, cast through an intermediate category that already has a path to primary:

   ```
   // Float -> Int (intermediate)
   FloatToInt . a:Float |- "int" "(" a ")" : Int ![a as i32] step;
   // Int -> Proc already exists
   ```

3. **Confirm the category is intentionally isolated.** If the category is used only
   as an internal building block (e.g., a helper category parsed only within specific
   rules of other categories), the warning can be acknowledged and ignored. Consider
   adding a comment in the grammar to document this intent.

4. **Remove the category.** If the category is unused and was declared by mistake,
   remove it from the `types { ... }` block and delete its associated rules. Note
   that G02 (unused-category) and G05 (empty-category) may also fire in this case.

## Hint Explanation

> add a cast rule from `{name}` to `{primary}` or an intermediate category

The hint directs the grammar author to create a bridge between the isolated category
and the primary category. A "cast rule" in PraTTaIL is a rule where the syntax
consists of a single non-terminal from a different category, effectively wrapping
that category's values into the result category. For example:

```
FloatToProc . a:Float |- a : Proc ![a.round() as i32] step;
```

This rule allows any `Float` expression to appear wherever a `Proc` expression is
expected, with the Rust code block `![...]` performing the type conversion.

The phrase "or an intermediate category" acknowledges that the cast graph is
transitive: if `Float -> Int` and `Int -> Proc` both exist, then `Float` has a path
to `Proc` and the lint will not fire. This can be preferable when a direct conversion
does not make semantic sense but a two-step conversion does.

## Related Lints

- [G02](./G02-unused-category.md) -- detects categories that are declared but never referenced by any rule; G08 is more specific, detecting categories that are referenced by their own rules but lack a path to primary
- [G05](./G05-empty-category.md) -- detects categories with zero rules, which trivially have no cast path (but G05 fires first)
- [C01](../cross-category/C01-cast-cycle.md) -- detects cycles in the cast graph; a cycle means infinite cast chains, while G08 detects disconnected subgraphs
- [C02](../cross-category/C02-transitive-cast-redundancy.md) -- detects redundant direct casts where a transitive path already exists; resolving G08 may introduce such redundancy
