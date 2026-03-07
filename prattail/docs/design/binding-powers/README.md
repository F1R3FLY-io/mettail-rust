# Binding Powers in PraTTaIL

This directory provides a unified, pedagogical treatment of PraTTaIL's **binding
power (BP) system** — the core mechanism governing operator precedence and
associativity across all operator forms.

## Documents

| # | Document                                                     | Topic                                                                       |
|---|--------------------------------------------------------------|-----------------------------------------------------------------------------|
| 1 | [01-fundamentals.md](01-fundamentals.md)                     | BP theory, core abstractions, the Pratt loop, asymmetry principle           |
| 2 | [02-implicit-deduction.md](02-implicit-deduction.md)         | Declaration-order precedence, the two-pass algorithm, three-level hierarchy |
| 3 | [03-explicit-specification.md](03-explicit-specification.md) | DSL annotations: `right`, `prefix(N)`, data flow                            |
| 4 | [04-operator-forms.md](04-operator-forms.md)                 | All operator types and their BP treatment                                   |
| 5 | [05-worked-examples.md](05-worked-examples.md)               | Complete walkthroughs with BP tables and parse traces                       |

## Quick-Reference: Operator Forms and BP Treatment

```
┌────────────────────┬──────────────────────────┬──────────────────────────────────┐
│ Operator Form      │ Structural Pattern       │ BP Assignment                    │
├────────────────────┼──────────────────────────┼──────────────────────────────────┤
│ Binary infix       │ a OP b : Cat             │ (2k, 2k+1) left-assoc            │
│ (left-associative) │                          │                                  │
├────────────────────┼──────────────────────────┼──────────────────────────────────┤
│ Binary infix       │ a OP b : Cat right       │ (2k+1, 2k) right-assoc           │
│ (right-associative)│                          │                                  │
├────────────────────┼──────────────────────────┼──────────────────────────────────┤
│ Unary prefix       │ OP a : Cat               │ prefix_bp = max_infix_bp + 2     │
│                    │                          │ (or explicit prefix(N))          │
├────────────────────┼──────────────────────────┼──────────────────────────────────┤
│ Postfix            │ a OP : Cat               │ left_bp = postfix_base + 1       │
│                    │                          │ right_bp = 0 (unused)            │
├────────────────────┼──────────────────────────┼──────────────────────────────────┤
│ Mixfix / N-ary     │ a OP₁ b OP₂ c : Cat      │ Same as infix (trigger terminal) │
│                    │                          │ Middle operands at min_bp=0      │
├────────────────────┼──────────────────────────┼──────────────────────────────────┤
│ Cross-category     │ a:CatA OP b:CatA : CatB  │ BPs in CatA's namespace          │
│                    │                          │ Dispatch wrapper in CatB         │
├────────────────────┼──────────────────────────┼──────────────────────────────────┤
│ Cast               │ k:CatA : CatB            │ No BP — prefix handler only      │
├────────────────────┼──────────────────────────┼──────────────────────────────────┤
│ Grouping           │ ( expr )                 │ Resets to min_bp=0               │
└────────────────────┴──────────────────────────┴──────────────────────────────────┘
```

## BP Number Line (per category)

```
BP:  0    2    4  ...  M   M+1  M+2   M+3  M+4  ...
     │    │    │       │    │    │      │    │
     │    └────┴── infix ───┘    │      └─── postfix ───
     │         range             │
     │                       prefix BP
   entry
  (min_bp)
```

Where M = max(left_bp, right_bp) across all non-postfix infix operators.

## Related Documentation

- [theory/pratt-parsing.md](../../theory/pratt-parsing.md) — Pratt algorithm from first principles
- [design/pratt-generator.md](../pratt-generator.md) — Generator design and codegen
- [usage/grammar-features.md](../../usage/grammar-features.md) — DSL syntax reference
- [design/disambiguation/03-operator-precedence.md](../disambiguation/03-operator-precedence.md) — Precedence as a disambiguation layer

## Key Source Files

| File                                                     | Content                                                    |
|----------------------------------------------------------|------------------------------------------------------------|
| `prattail/src/binding_power.rs`                          | BP types, `analyze_binding_powers()` algorithm             |
| `prattail/src/classify.rs`                               | Structural classification (infix/prefix/postfix detection) |
| `prattail/src/lib.rs:241-295`                            | `RuleSpec` with BP-related fields                          |
| `prattail/src/pipeline.rs:1111-1236`                     | BP table computation, prefix BP assignment                 |
| `prattail/src/pratt.rs`                                  | Pratt loop codegen, led chain, BP lookup functions         |
| `macros/src/ast/grammar.rs:97-340`                       | DSL parsing of `right` and `prefix(N)`                     |
| `macros/src/gen/syntax/parser/prattail_bridge.rs:84-123` | Bridge: `GrammarRule` → `RuleSpecInput`                    |
