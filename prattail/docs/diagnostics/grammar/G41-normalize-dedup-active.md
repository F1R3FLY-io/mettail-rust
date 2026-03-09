# G41: normalize-dedup-active

**Severity:** Note
**Category:** grammar
**Feature Gate:** None (always enabled)

## Description

Reports that the BCG05 normalize-on-insert deduplication optimization is active.
Hash-based dedup guards have been emitted in the generated Ascent code for all
category rules and rewrite/equation rules. These guards compute a structural
hash of each term before inserting it into an Ascent relation, skipping the
insertion if an identical term (by hash) has already been added in the current
epoch.

The Ascent fixpoint engine processes rules iteratively until no new tuples are
produced. Without dedup guards, the same logically-equivalent term may be
re-derived and re-inserted on multiple iterations, triggering redundant
`normalize()` calls and downstream rule firings. The BCG05 optimization
interposes a hash check: if the term's structural hash matches an already-
inserted term, the insertion is skipped, avoiding redundant normalization work.

```
  Dedup guard flow:

  ┌──────────────────────────────┐
  │  Ascent rule derives term t  │
  │                              │
  │  hash(t) ∈ inserted_set?     │
  │  ├── yes -> skip insertion   │
  │  │         (no normalize,    │
  │  │          no downstream    │
  │  │          rule firings)    │
  │  │                           │
  │  └── no  -> insert t         │
  │             add hash(t)      │
  │             normalize(t)     │
  │             fire downstream  │
  └──────────────────────────────┘
```

The dedup guards are implemented as thread-local `HashSet<u64>` that are cleared
at the start of each Ascent evaluation (epoch boundary). This ensures that
dedup is scoped to a single evaluation and does not interfere with incremental
or re-entrant evaluation.

## Trigger Conditions

All of the following must hold:

- The grammar defines at least one equation or rewrite rule.
- The `language!` macro expansion reaches the BCG05 diagnostic emission point
  (always, after antipattern detection).
- At least one rule and one category exist.

One diagnostic is emitted per grammar.

## Example

### Grammar

```rust
language! {
    name: CalcLang,
    types {
        ![i32] as Expr
    },
    terms {
        Num . n:Expr |- n            : Expr;
        Add . a:Expr, b:Expr |- a "+" b : Expr;
    },
    equations {
        Num(n) = n;
        Add(a, b) = a + b;
    },
}
```

### Output

```
note[G41] (CalcLang): BCG05 normalize-on-insert dedup: hash guards emitted for 2 rule(s) across 1 category(ies)
  = hint: structural hash pre-check avoids redundant normalize() calls in the Ascent fixpoint
```

## Resolution

No action required. G41 is an informational diagnostic confirming that the
BCG05 optimization is active. The dedup guards are generated unconditionally
and provide a strict improvement in fixpoint evaluation efficiency.

If hash collisions are suspected (rare but theoretically possible):

1. **Inspect fixpoint convergence.** If the Ascent evaluation produces
   incorrect results, verify that the hash function does not produce
   false-positive collisions for distinct terms. The current implementation
   uses `std::hash::Hash` on the full term structure.

2. **Disable for debugging.** The dedup guards cannot be individually disabled
   at runtime, but the generated Ascent source file (if written successfully;
   see I10) can be inspected to verify that the guards are correctly placed.

## Hint Explanation

The hint **"structural hash pre-check avoids redundant normalize() calls in
the Ascent fixpoint"** explains the optimization's benefit: by checking a
structural hash before insertion, the system avoids calling `normalize()` on
terms that have already been processed. Since `normalize()` is the most
expensive per-term operation in the Ascent fixpoint (it traverses the
equivalence class to find a canonical representative), skipping it for
duplicate terms provides significant savings in grammars with many congruence
or equation rules.

## Related Lints

- [G35](G35-ground-rewrite-short-circuit.md) -- Ground rewrite short-circuit.
  Complements G41: ground rewrites are seeded at init, and dedup guards
  prevent re-seeding on subsequent iterations.
- [G38](G38-bloom-filter-rw-congruence-guard.md) -- Bloom filter rewrite
  congruence guard. Discriminant pre-checks reduce the number of terms
  reaching the dedup guard.
- [G42](G42-eq-strata-analysis.md) -- Equation stratification. Stratification
  reduces cross-stratum redundancy, complementing per-insertion dedup.
- [I18](../infrastructure/I18-lint-cache-hit.md) -- Lint cache hit. Another
  caching optimization (at the diagnostic level rather than the term level).
