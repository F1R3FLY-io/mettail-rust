# RA01-SKIP: Register Dead Binder Elimination

Advanced Automata Codegen Optimization — M6 Register → Skip Alpha-Equivalence

## 1. Quick Start

**What it does**: Skips alpha-equivalence checking for binder categories
where register analysis proves the bound variable is stored but never
tested. If a variable is bound but never pattern-matched against,
tracking its identity is unnecessary.

**When it activates**: When the `register-automata` feature is enabled and
`RegisterAnalysis.dead_registers` is non-empty.

**Feature gate**: `register-automata`

**Optimization gate**: `skip_dead_binders` (env: `PRATTAIL_OPT_SKIP_DEAD_BINDERS`)

**Status**: `OptimizationStatus::Auto`

**New PipelineAnalysis field**: `dead_binder_categories: HashSet<String>`

## 2. Intuition

Consider a lambda calculus grammar:

```
rule lambda:  "λ" Binder "." Body
rule apply:   Expr Expr
rule var:     Identifier
```

If the grammar never uses pattern-matching on bound variables (no
`TestEq`/`TestNeq` transitions in the register automaton), then the
binder's identity is irrelevant to parsing — it's stored but never
consulted.

Alpha-equivalence checking (verifying that `λx.x` and `λy.y` are
equivalent) is expensive: it requires maintaining De Bruijn indices and
performing recursive comparisons. RA01-SKIP eliminates this cost for
dead-register binders.

```
Register automaton for Binder:
  q0 →[name] Store(0) → q1 →[body] Nop → q2 (accept)

Register 0: Store transitions: 1, Test transitions: 0 → DEAD

Result: skip alpha-equiv for Binder category
```

## 3. Theory

A register rᵢ is *dead* if it has Store transitions but no TestEq,
TestNeq, or TestFresh transitions (Kaminski & Francez 1994). A dead
register's value cannot influence acceptance — the automaton behaves
identically regardless of what value rᵢ holds.

Formally: Let RA' be RA with all Store(i) replaced by Nop. Then
L(RA) = L(RA'), because no transition guards on rᵢ's value.

See [codegen-soundness.md](../theory/optimization/codegen-soundness.md) §6.

## 4. Implementation

Dead register indices are mapped to binder category names:

```
for each dead register index i in register_result.dead_registers:
    if let Some(category) = categories.get(i):
        dead_binder_categories.insert(category.name)
```

Out-of-bounds indices (where `i >= categories.len()`) are gracefully
skipped via `categories.get(i)` returning `None`.

## 5. Diagnostics

- **RA01** (unbound-data-reference): Related register analysis lint
- **RA02** (redundant-register): Fires when a register is detected as dead

## 6. Future Work

Wire `dead_binder_categories` into the macros crate's binder alpha-equiv
codegen (where `Binder` or `alpha` code is emitted in `macros/src/logic/mod.rs`).
Currently the field is populated in `PipelineAnalysis` but the macros crate
does not yet read it.

## 7. Related

- [Register Automata Design](../design/register-automata.md) — Full M6 design
- [SYM01-DCE](SYM01-DCE.md) — Another dead-code elimination optimization
