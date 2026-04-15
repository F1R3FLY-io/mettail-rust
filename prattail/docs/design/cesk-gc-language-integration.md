# CESK GC Language Integration: Design Review

## Overview

This document describes the proposed `language!` macro syntax for configuring GC strategy per-language. This is a **design review** — the implementation is deferred to a future sprint.

## Proposed DSL Syntax

```rust
language! {
    name: MyLang;

    gc {
        strategy: ref_count;   // or: mark_sweep, none
        // Optional mark-sweep parameters (ignored for ref_count/none):
        // interval: 100ms;
        // threshold: 10mb;
    }

    // ... types, rules, etc.
}
```

## Strategy Options

| Syntax | Enum | When to Use |
|--------|------|-------------|
| `strategy: none;` | `GcStrategy::None` | Calculator, short-lived evals |
| `strategy: ref_count;` | `GcStrategy::RefCount` | Lambda calculus, closures (default) |
| `strategy: mark_sweep;` | `GcStrategy::MarkSweep` | Rho-calculus, channels, tuplespace |

## Grammar Integration

The `gc { ... }` block would be parsed by `macros/src/ast/language.rs` alongside existing blocks (`types`, `rules`, `channels`, `tokens`). The parsed `GcConfig` flows through:

1. `LanguageDef::gc_config` — AST node
2. `LanguageSpec::gc_strategy` — bridge to prattail
3. `generate_language_impl()` — codegen wires GcStrategy to CekEvaluator construction

## Impact on Existing Languages

All four current languages (Calculator, Lambda, Ambient, RhoCalc) would continue to work unchanged — the `gc` block is optional, defaulting to `GcStrategy::RefCount`.

Recommended per-language strategies:
- **Calculator**: `none` (step-limited, no closures)
- **Lambda**: `ref_count` (closures but no cycles)
- **Ambient/RhoCalc**: `mark_sweep` (channels, shared mutable state)
