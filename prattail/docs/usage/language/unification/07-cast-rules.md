# Category Embeddings via Cast Rules

## Intuition

"Cast rules embed one type system into another -- a `Name` can appear wherever
a `Proc` is expected." Cast rules are the simplest form of implicit
cross-category composition: they allow values of one category to be used
transparently in another category's parse context.

## Why Important

- Multi-sort languages with subtyping relationships
- Type coercion: integers appearing in process contexts
- Category hierarchies: Name ⊂ Proc, Int ⊂ Float

## Syntax

```rust
CastInt . k:Int |- k : Proc;      // Int can appear where Proc is expected
IntToFloat . k:Int |- k : Float;  // Int can appear where Float is expected
```

A cast rule has exactly ONE nonterminal operand of a different category than
the result. No additional terminals.

## Category Reachability Graph

Cast rules create a directed graph over categories:

```
  Int ──cast──▶ Float ──cast──▶ Str
   │                              ▲
   └──────────cast────────────────┘
```

Transitive closure: if Int → Float → Str, then Int values are transitively
reachable in Str contexts. The Tier 2 dead-rule analysis computes this
fixed-point to determine category reachability.

**Formal definition**:
```
R = μX. { C | FIRST(C) ≠ ∅ }
       ∪ { C | ∃ cast/cross-cat rule r : r.source ∈ X ∧ r.target = C }
```

## Dead-Rule Interaction

Cast rules interact with dead-rule detection at multiple tiers:

**Tier 2 (Category Reachability)**: Cast edges propagate reachability. If
category A is reachable and there's a cast from A to B, then B becomes
reachable too:
```
Int reachable (has Integer token in FIRST set)
    │
    ├── IntToFloat cast ──▶ Float becomes reachable
    │
    └── IntToStr cast ──▶ Str becomes reachable
```

**Tier 3 (WFST Dispatch)**: A cast rule is dead if the WFST routes every FIRST
token to higher-priority alternatives. Example: `FloatToStr` is dead if
`IntToStr` and `StrLit` handle all Str-reachable tokens first.

## WFST Weight Assignment

Cast rules receive tropical weights based on specificity:
- Direct parse (e.g., `StrLit` for `"..."`) gets lowest weight (highest priority)
- Shorter cast chains get lower weight than longer ones
- Weight ordering: direct > single-cast > double-cast > ...

## Cast Cycle Detection (Lint C01)

Circular cast chains are detected by lint C01:
```
Int ──cast──▶ Float ──cast──▶ Int    // Cycle! C01 warning
```

The lint constructs a directed graph and detects cycles via DFS. Cast cycles
indicate a grammar design error -- they create infinite parse loops.

## Transitive Cast Redundancy (Lint C02)

If cast Int → Float and Int → Str both exist, AND Float → Str also exists,
then Int → Str is redundant (it can be achieved transitively via
Int → Float → Str). Lint C02 detects this:
```
Int ──cast──▶ Float ──cast──▶ Str
 │                               ▲
 └──────────cast─────────────────┘  ← C02: redundant (transitive path exists)
```

## Diagrams

**Reachability propagation:**
```
  Seed: categories with non-empty FIRST sets
  ┌─────┐
  │ Int │  FIRST = {Integer, Ident}     ← seed
  └──┬──┘
     │ IntToFloat cast
     ▼
  ┌───────┐
  │ Float │  FIRST = {Integer, Ident}   ← reachable via cast
  └──┬────┘
     │ FloatToStr cast
     ▼
  ┌─────┐
  │ Str  │  FIRST = {Integer, Ident, StringLit}  ← reachable via transitive cast
  └─────┘

  Fixed-point: 2 iterations (cast propagation stabilizes)
```

**Cast chain depth and dispatch priority:**
```
  Token: Integer
  ┌───────────────────────────────────────┐
  │ Dispatch for Str category:            │
  │                                       │
  │  1. StrLit  (direct, w=0.1)     ← hot│
  │  2. IntToStr (1 cast, w=0.5)         │
  │  3. FloatToStr (2 casts, w=0.9) ← cold│
  └───────────────────────────────────────┘
```

## Integration

Cast rules participate in:
1. **FIRST set analysis**: cast source FIRST tokens are added to target category's FIRST set
2. **Dispatch generation**: cast rules produce match arms in the Pratt prefix handler
3. **Dead-rule detection**: Tier 2 uses cast edges for reachability; Tier 3 checks WFST dispatch
4. **Lint layer**: C01 (cast cycles), C02 (transitive redundancy), P03 (deep cast nesting)

## Critical Implementation Detail

Cast rules are placed in the Pratt PREFIX handler, not in dispatch wrappers.
This ensures the Pratt infix loop continues after a cast parse completes, so
operators following a cast expression are handled correctly.

## Source Reference

| Component | File |
|-----------|------|
| Cast rule classification | `prattail/src/lib.rs` (RuleSpec.is_cast) |
| Category reachability | `prattail/src/pipeline.rs` |
| WFST weight assignment | `prattail/src/pipeline.rs` |
| Cast cycle detection (C01) | `prattail/src/lint.rs` |
| Transitive redundancy (C02) | `prattail/src/lint.rs` |
| Dispatch generation | `prattail/src/dispatch.rs` |
