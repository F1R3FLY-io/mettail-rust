# G04: duplicate-rule-label

**Severity:** Error
**Category:** Grammar Structure

## Description

Detects duplicate rule labels within the same category. Each rule label is used as the constructor name in the generated AST enum variant, so two rules with the same (category, label) pair produce conflicting Rust enum variant names, conflicting parse dispatch branches, and ambiguous AST construction. This is a correctness error that prevents valid code generation.

## Trigger Conditions

An error is emitted when the same `(category, label)` pair appears more than once across all entries in `ctx.all_syntax`. The check uses a `HashMap` to track seen pairs -- the first occurrence is recorded, and any subsequent occurrence with an identical key triggers the diagnostic.

Note: rules with the same label in **different** categories do not trigger this lint, since each category produces a separate enum type (e.g., `Int::Add` and `Float::Add` are distinct constructors).

## Example

### Grammar

```
language! {
    name: DuplicateCalc,
    types {
        ![i32] as Int
        ![bool] as Bool
    },
    terms {
        Add . a:Int, b:Int |- a "+" b : Int ![a + b] fold;
        Sub . a:Int, b:Int |- a "-" b : Int ![a - b] fold;

        // ERROR: "Add" already exists in category Int
        Add . a:Int, b:Int |- a "++" b : Int ![a + b] fold;

        // OK: "Add" in Bool is a different category
        Add . a:Bool, b:Bool |- a "+" b : Bool ![a || b] step;
    },
}
```

The second `Add` rule targeting `Int` conflicts with the first. The `Add` rule targeting `Bool` is fine because it occupies a separate namespace.

### Output

```
error[G04]: duplicate rule label `Add` in category `Int` — codegen will produce conflicting constructor names
  --> <macro>:12:9
  = in category `Int`, rule `Add`
  = hint: rename one of the rules to a unique label
```

## Resolution

Rename one of the conflicting rules to a unique label within that category:

```
language! {
    name: FixedCalc,
    types {
        ![i32] as Int
        ![bool] as Bool
    },
    terms {
        Add . a:Int, b:Int |- a "+" b : Int ![a + b] fold;
        Sub . a:Int, b:Int |- a "-" b : Int ![a - b] fold;

        // Renamed from "Add" to "Concat" to avoid conflict
        Concat . a:Int, b:Int |- a "++" b : Int ![a + b] fold;

        // Still OK: different category
        Add . a:Bool, b:Bool |- a "+" b : Bool ![a || b] step;
    },
}
```

Choose labels that accurately describe the semantic operation of each rule. When two rules perform similar operations with different syntax (e.g., `"+"` vs `"++"` for addition), use labels that distinguish the syntax or semantics (e.g., `Add` vs `Concat`, or `AddArith` vs `AddBitwise`).

## Hint Explanation

The hint "rename one of the rules to a unique label" is the only valid resolution. Unlike warnings, which may have multiple mitigation strategies, a duplicate rule label is an unrecoverable codegen error. The generated Rust code emits an `enum` variant for each rule label within a category:

```rust
enum Int {
    Add(Box<Int>, Box<Int>),    // first Add rule
    Add(Box<Int>, Box<Int>),    // second Add rule -- compile error!
    Sub(Box<Int>, Box<Int>),
}
```

Rust does not permit duplicate enum variant names, so the generated code will fail to compile. Additionally, the parser dispatch table maps each label to a parsing function -- duplicate labels produce conflicting entries. The fix is strictly to ensure uniqueness of labels within each category.

## Related Lints

- [G07](./G07-identical-rules.md) -- detects rules that are structurally identical (same syntax items) but may have different labels; the inverse situation where the *content* is duplicated rather than the *name*
