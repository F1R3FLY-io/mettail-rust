# G05: empty-category

**Severity:** Warning
**Category:** Grammar Structure

## Description

Detects categories that are declared in the `types` block but have zero rules producing into them. An empty category generates an enum with no variants, a parse function that can never succeed, and a lexer configuration with no dispatchable tokens. Any attempt to parse a value of an empty category will unconditionally fail at runtime. This typically indicates a grammar that is incomplete or a category that was declared prematurely.

## Trigger Conditions

A warning is emitted when a category satisfies **both** of the following:

1. The category name appears in `ctx.categories` (i.e., it was declared in the `types` block).
2. No entry in `ctx.all_syntax` has this category as its target (i.e., no `(label, category, syntax)` triple exists where `category` matches the empty category name).

This lint fires based solely on whether rules **produce into** the category. A category could be referenced as a NonTerminal in other rules' syntax items (and thus not trigger G02) while still being empty (no rules of its own).

## Example

### Grammar

```
language! {
    name: IncompleteLang,
    types {
        ![i32] as Int
        ![bool] as Bool
        Proc                // Declared but no rules produce a Proc
    },
    terms {
        Add . a:Int, b:Int |- a "+" b : Int ![a + b] fold;
        Neg . a:Int |- "-" a : Int ![(-a)] fold;
        GtInt . a:Int, b:Int |- a ">" b : Bool ![a > b] step;
        Not . a:Bool |- "not" a : Bool ![!a] step;

        // This rule references Proc as a NonTerminal (so Proc is not unused),
        // but Proc itself has zero rules -- it can never be parsed.
        Run . p:Proc |- "run" p : Int;
    },
}
```

In this grammar, `Proc` is referenced by the `Run` rule's syntax (so G02 does not fire), but no rule produces a `Proc` value, so `parse_Proc()` can never succeed.

### Output

```
warning[G05]: category `Proc` has zero rules — cannot be parsed
  = in category `Proc`
  = hint: add at least one rule or remove the category declaration
```

## Resolution

1. **Add rules for the empty category.** If the category is intended to be part of the grammar, define at least one rule that produces into it:
   ```
   terms {
       // ... existing rules ...

       // Now Proc has rules:
       Print . val:Int |- "print" "(" val ")" : Proc;
       Seq . first:Proc, second:Proc |- first ";" second : Proc;
   },
   ```

2. **Remove the category declaration** if it was declared prematurely or by mistake:
   ```
   types {
       ![i32] as Int
       ![bool] as Bool
       // Proc removed -- also remove any rules referencing it
   },
   ```

3. **Check for misspelled category names.** If rules intended to target this category use a slightly different spelling, fix the mismatch. For example, if `Process` was used instead of `Proc` in rule targets, unifying the name resolves both the empty category and any "undeclared category" errors.

## Hint Explanation

The hint "add at least one rule or remove the category declaration" captures the two valid resolutions for an empty category. A category with zero rules generates a parse function that immediately fails -- it cannot match any input. Adding a rule gives the category at least one production, making it parseable. Removing the declaration eliminates the dead code entirely. The lint does not distinguish between a category that was intentionally left empty (e.g., as a placeholder during incremental grammar development) and one that is empty by mistake, so the grammar author must decide which action is appropriate.

## Related Lints

- [G02](./G02-unused-category.md) -- detects categories that are never *referenced* by other rules' syntax items; a category can be empty (G05) yet still referenced, or unused (G02) yet have rules producing into it; both lints can fire simultaneously for a category that is both unreferenced and has no rules
- [G08](./G08-missing-cast-to-root.md) -- a non-empty category that lacks a cast path to the primary (root) category may be parseable but unreachable from the top-level entry point, a related integration concern
