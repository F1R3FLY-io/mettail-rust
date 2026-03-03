# G02: unused-category

**Severity:** Warning
**Category:** Grammar Structure

## Description

Detects categories that are declared in the `types` block but never referenced by any rule's syntax items. An unused category adds dead code to the generated parser: enum variants, parse functions, and lexer tokens are emitted for it, but no rule ever produces or consumes values of that category. This wastes compile time, increases binary size, and signals a likely authoring mistake (typo in category name, forgotten rule, or leftover from refactoring).

## Trigger Conditions

A warning is emitted when a category satisfies **both** of the following:

1. The category name appears in `ctx.categories` (i.e., it was declared in the `types` block).
2. The category name does **not** appear in any of the following positions across all rules in `ctx.all_syntax`:
   - As the `category` field of a `NonTerminal` syntax item.
   - As the `element_category` field of a `Collection` syntax item.
   - As the `left_category` or `right_category` field of a `ZipMapSep` syntax item.
   - As the `category` field of a `Binder` syntax item.
   - Recursively inside an `Optional { inner }` syntax item.
   - As the target category of any rule (i.e., the category a rule produces into).

A category that has rules targeting it (producing values of that type) but is never consumed by another rule's syntax is still considered "referenced" because the rules themselves reference it as a target. The lint fires only when a category has zero inbound references of any kind.

## Example

### Grammar

```
language! {
    name: MiniCalc,
    types {
        ![i32] as Int
        ![f64] as Float
        ![bool] as Bool
        ![str] as Str     // Declared but never used in any rule
    },
    terms {
        Add . a:Int, b:Int |- a "+" b : Int ![a + b] fold;
        Sub . a:Int, b:Int |- a "-" b : Int ![a - b] fold;
        Neg . a:Int |- "-" a : Int ![(-a)] fold;
        ToFloat . a:Int |- "float" "(" a ")" : Float ![a as f64] step;
        GtInt . a:Int, b:Int |- a ">" b : Bool ![a > b] step;
    },
}
```

In this grammar, `Str` is declared but no rule references it as a NonTerminal argument, Collection element, Binder category, or rule target. The `Int`, `Float`, and `Bool` categories are all referenced (as rule targets and/or syntax items).

### Output

```
warning[G02]: category `Str` declared but never referenced in any rule syntax
  = in category `Str`
  = hint: remove the unused category or add rules that reference it
```

## Resolution

1. **Remove the category** if it is genuinely unused. Delete its declaration from the `types` block:
   ```
   types {
       ![i32] as Int
       ![f64] as Float
       ![bool] as Bool
       // Str removed
   },
   ```

2. **Add rules that reference it** if the category was intended to be used. For example, add string literals, concatenation, or type-cast rules:
   ```
   Concat . a:Str, b:Str |- a "++" b : Str ![[a, b].concat()] step;
   IntToStr . a:Int |- "str" "(" a ")" : Str ![a.to_string()] step;
   ```

3. **Fix a typo** if the category was referenced but under a different name. Ensure the `types` declaration and all rule syntax items use the same spelling.

## Hint Explanation

The hint "remove the unused category or add rules that reference it" presents the two possible intentions behind an unused category. If the category was declared by mistake or is a remnant of a prior grammar revision, removing it eliminates dead code in the generated parser. If the category is intentional but the rules that reference it are missing or misspelled, adding those rules completes the grammar. The lint cannot distinguish between these cases, so it surfaces the issue for the grammar author to decide.

## Related Lints

- [G05](./G05-empty-category.md) -- a category with zero rules (no rule produces into it) is a stricter version of this lint; a category can be unused (G02) yet still have rules producing into it, or it can be empty (G05) yet still be referenced by other rules' syntax items
- [G08](./G08-missing-cast-to-root.md) -- a category that is referenced but has no cast path to the root category may indicate an integration gap similar to an unused category
