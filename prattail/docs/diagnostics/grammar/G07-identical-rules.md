# G07: identical-rules

**Severity:** Warning
**Category:** Grammar Structure

## Description

Detects multiple rules within the same category that have structurally identical
syntax item sequences. Two rules are considered identical when their normalized
representations match exactly, comparing:

- `Terminal(t)` -- the literal terminal string
- `NonTerminal { category }` -- the category name (field names are ignored)
- `IdentCapture` -- identity capture slots
- `Binder { category, is_multi }` -- binder category and multiplicity
- `Collection { element_category, separator, kind }` -- element type, separator string, and collection kind
- `ZipMapSep { left_category, right_category, body_items, separator }` -- both categories, recursively normalized body, and separator
- `BinderCollection { separator }` -- separator string
- `Optional { inner }` -- recursively normalized inner items

When two rules produce the same normalized signature, they are syntactically
indistinguishable to the parser: no token sequence can uniquely select one over the
other. This means the parser will always dispatch to one and never the other, or
the WFST will assign arbitrary weights between them. Either way, one rule is
effectively dead code.

## Trigger Conditions

The lint fires when **all** of the following conditions hold:

1. Two or more rules belong to the same category.
2. Their syntax item sequences produce the same string under `syntax_signature()`,
   which normalizes each `SyntaxItemSpec` variant to a canonical form (stripping
   field names, Rust code blocks, and label names).
3. The rules have different labels (same-label duplicates are caught by G04).

The signature function recurses into `ZipMapSep.body_items` and `Optional.inner`
to ensure nested structures are compared faithfully.

## Example

### Grammar

```
language! {
    name: Calc,
    types {
        ![i32] as Int
        ![bool] as Bool
    },
    terms {
        AddInt   . a:Int, b:Int |- a "+" b : Int  ![a + b] fold;
        PlusInt  . x:Int, y:Int |- x "+" y : Int  ![x + y] fold;
        SubInt   . a:Int, b:Int |- a "-" b : Int  ![a - b] fold;
        EqInt    . a:Int, b:Int |- a "==" b : Bool ![a == b] step;
    }
}
```

Here, `AddInt` and `PlusInt` have identical syntax: both are `NT(Int) | T(+) | NT(Int)`.
The different field names (`a`/`b` vs `x`/`y`) and different labels do not affect
the normalized signature. The parser cannot distinguish them because no token
sequence would match one but not the other.

### Output

```
warning[G07]: rules [AddInt, PlusInt] in category `Int` have identical syntax item sequences
  = in category `Int`
  = hint: these rules are structurally identical — consider merging or differentiating their syntax
```

## Resolution

To resolve this warning, choose one of the following strategies:

1. **Merge the rules.** If both rules compute the same result, delete one and keep
   the other. This is the most common resolution.

   ```
   // Keep only one:
   AddInt . a:Int, b:Int |- a "+" b : Int ![a + b] fold;
   ```

2. **Differentiate the syntax.** If the rules are meant to express different
   semantics, add a distinguishing terminal token:

   ```
   AddInt    . a:Int, b:Int |- a "+"  b : Int ![a + b] fold;
   SaturAdd  . a:Int, b:Int |- a "+?" b : Int ![a.saturating_add(b)] fold;
   ```

3. **Move to different categories.** If the rules serve different type-level
   purposes, place them in separate categories:

   ```
   AddInt   . a:Int, b:Int   |- a "+" b : Int   ![a + b] fold;
   AddFloat . a:Float, b:Float |- a "+" b : Float ![a + b] fold;
   ```
   (These are already in different categories via their result types, so this
   situation does not trigger G07.)

## Hint Explanation

> these rules are structurally identical -- consider merging or differentiating their syntax

The hint points out that the parser's dispatch mechanism (whether WFST-weighted or
token-based) cannot distinguish between the two rules because their terminal and
non-terminal structure is identical. This means:

- **WFST dispatch** will assign arbitrary or equal weights to both rules, leading to
  non-deterministic selection.
- **Token-based dispatch** will always match the first rule encountered and never
  reach the second.
- **Dead-rule detection** (W01) may independently flag one of the rules as
  unreachable.

The recommended action is to merge them into a single rule (if they compute the same
thing) or to add a distinguishing terminal token (if they represent different
operations).

## Related Lints

- [G04](./G04-duplicate-rule-label.md) -- detects duplicate rule *labels* (names) within a category, which is a stricter form of duplication (Error severity) compared to G07's structural duplication (Warning severity)
