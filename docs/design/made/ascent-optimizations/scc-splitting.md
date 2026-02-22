# Opt 5: SCC Splitting (Core/Full Fixpoint Equivalence)

## 1. Motivation

Multi-category languages generate large Ascent structs with rules for every reachable `(src, tgt)` category pair. For example, RhoCalc with 6 categories generates rules for all reachable cross-category subterm extractions, congruence propagations, and rewrite expansions.

However, common inputs — like a `Proc` term being rewritten — only ever populate `Proc` and `Name` relations. Categories like `Expr`, `Chan`, `Ground`, and `Float` remain empty throughout the fixpoint computation. The full struct still evaluates rules targeting these empty categories, wasting cycles.

**SCC splitting** generates a smaller **Core** Ascent struct containing only rules between "core" categories (those bidirectionally reachable from the primary category). For core-category inputs, the smaller struct runs a faster fixpoint. Non-core inputs fall back to the full struct.

**Concern:** Does the Core fixpoint produce the same results as the Full fixpoint restricted to core categories?

## 2. The Optimization

### 2.1 Core Category Computation

Core categories are bidirectionally reachable from the primary (first-declared) category:

```rust
// common.rs:357-391
pub fn compute_core_categories(language: &LanguageDef) -> Option<BTreeSet<String>> {
    let reachable = compute_category_reachability(language);
    let primary = all_cats.first()?.clone();

    let mut core = BTreeSet::new();
    core.insert(primary.clone());

    for cat in &all_cats {
        if *cat == primary { continue; }
        // Both primary→cat AND cat→primary must exist
        if reachable.contains(&(primary.clone(), cat.clone()))
            && reachable.contains(&(cat.clone(), primary.clone()))
        {
            core.insert(cat.clone());
        }
    }

    // No benefit if core == all categories
    if core.len() == all_cats.len() {
        return None;
    }
    Some(core)
}
```

### 2.2 Two Ascent Structs

When `compute_core_categories` returns `Some(core)`, the code generator produces two Ascent structs:

1. **Core struct** (`{Lang}AscentProgCore`): Rules only between categories in `core`
2. **Full struct** (`{Lang}AscentProg`): All rules (unchanged)

### 2.3 Dispatcher Routing

The `run_ascent_typed` method routes inputs based on their category:

```rust
// language.rs:1254-1288
match &term.0 {
    Inner::Ambiguous(alts) => { /* handle ambiguity */ }

    // Core categories: use the smaller core struct
    Inner::Proc(_) | Inner::Name(_) => {
        let mut prog = LangAscentProgCore::default();
        // seed + run + extract (core struct)
        prog.run();
    }

    // Non-core categories: use the full struct
    _ => {
        let mut prog = LangAscentProg::default();
        // seed + run + extract (full struct)
        prog.run();
    }
}
```

**Implementation:** `language.rs:1173-1312`

## 3. Formal Model

### 3.1 Core Categories

**Definition (is_core).** A category `c` is core if it is bidirectionally reachable from the primary:

```
is_core(c) := bidi_reach(primary, c)
             = reach(primary, c) ∧ reach(c, primary)
```

**Definition (core_cats).** The set of core categories:

```
core_cats := filter (λ c. is_core(c)) all_cats
```

**Lemma (primary_is_core).** The primary category is always core:

> `is_core(primary)`

**Proof.** `bidi_reach(primary, primary)` holds by `reach_refl` in both directions. **QED.**

### 3.2 Database and Derivation

**Definition (DB).** A database maps each category to a list of facts. Operations: `get_rel`, `set_rel`, `empty_db`.

**Definition (derive).** `derive(src, tgt, db)` applies the rule for `(src, tgt)` to the database, producing new `tgt`-typed facts.

**Definition (non_core_empty).** The key invariant — all non-core category relations are empty:

```
non_core_empty(db) := ∀ c, ¬is_core(c) → get_rel(db, c) = []
```

### 3.3 Step Functions

**Definition (full_step).** The immediate consequence operator using all rules:

```
full_step(db, tgt) := flat_map (λ src. derive(src, tgt, db)) all_cats
```

**Definition (core_step).** The immediate consequence operator using only core-to-core rules:

```
core_step(db, tgt) := flat_map (λ src. derive(src, tgt, db)) core_cats
```

**Definition (full_iter, core_iter).** Single iteration via merge:

```
full_iter(db) := merge_step(db, full_step(db))
core_iter(db) := merge_step(db, λ c. if is_core(c) then core_step(db, c) else [])
```

**Definition (full_iter_n, core_iter_n).** N-step iteration:

```
full_iter_n(0, db)   := db
full_iter_n(S n, db) := full_iter(full_iter_n(n, db))
```

## 4. Key Hypotheses

| Hypothesis | Statement | Justification |
|------------|-----------|---------------|
| `derive_from_empty` | `get_rel(db, src) = [] → derive(src, tgt, db) = []` | If a source category has no facts, no rule with that source can fire. The generated `flat_map` over an empty list produces `[]`. |
| `derive_unreachable_empty` | `¬reach(src, tgt) → derive(src, tgt, db) = []` | From Opt 3 (Dead Rule Pruning): unreachable rules derive nothing. The code generator does not emit match arms for unreachable pairs. |
| `derive_core_noncore_empty` | `is_core(src) ∧ ¬is_core(tgt) ∧ non_core_empty(db) → derive(src, tgt, db) = []` | If `src` is core and `tgt` is non-core, the extraction path `src → ... → tgt` must pass through at least one non-core intermediate category (since core categories only have edges to core categories by the closure property). The join on that intermediate yields nothing because its relation is empty. |
| `merge_preserves_noncore_empty` | `non_core_empty(db) ∧ (∀ c, ¬is_core(c) → step(c) = []) → non_core_empty(merge(db, step))` | Merging empty facts into empty relations preserves emptiness. The merge function is additive — it can only add facts, not remove them. |
| `merge_ext` | `(∀ c, f(c) = g(c)) → merge_step(db, f) = merge_step(db, g)` | Merge is extensional: if two step functions agree pointwise, the merged databases are identical. |

## 5. Theorems and Proofs

### 5.1 S1: Non-Core Targets Derive Nothing

**Theorem (S1: non_core_derives_nothing).**

> `∀ tgt db, ¬is_core(tgt) → non_core_empty(db) → full_step(db, tgt) = []`

**Proof.** Unfold `full_step`. Apply `flat_map_all_nil`. For each source category `src`:

- **Case `is_core(src)`:** Source is core, target is non-core. By `derive_core_noncore_empty`, `derive(src, tgt, db) = []`. **QED.**
- **Case `¬is_core(src)`:** Source is non-core. By `non_core_empty(db)`, `get_rel(db, src) = []`. By `derive_from_empty`, `derive(src, tgt, db) = []`. **QED.**

Since every source produces `[]`, `flat_map` produces `[]`. **QED.**

### 5.2 S2: Core Derivations Identical

**Theorem (S2: core_derivations_equal).**

> `∀ tgt db, is_core(tgt) → non_core_empty(db) → full_step(db, tgt) = core_step(db, tgt)`

**Proof.** Unfold `full_step` and `core_step`. The difference is the domain of `flat_map`: `all_cats` vs `core_cats = filter is_core all_cats`.

Apply `flat_map_filter_nil`. For each source `src` that was filtered out (`¬is_core(src)`), we show `derive(src, tgt, db) = []`:

- Source is non-core. By `non_core_empty(db)`, `get_rel(db, src) = []`. By `derive_from_empty`, derivation is `[]`. **QED.**

Since removed elements contribute `[]`, the results are identical. **QED.**

### 5.3 Invariant Preservation

**Lemma (full_iter_preserves_invariant).**

> `∀ db, non_core_empty(db) → non_core_empty(full_iter(db))`

**Proof.** Unfold `full_iter`. Apply `merge_preserves_noncore_empty`:
1. `non_core_empty(db)` holds by assumption.
2. For each non-core `c`, `full_step(db, c) = []` by S1. **QED.**

**Lemma (full_iter_n_preserves_invariant).**

> `∀ n db, non_core_empty(db) → non_core_empty(full_iter_n(n, db))`

**Proof.** Induction on `n`:
- **Base (`n = 0`):** `full_iter_n(0, db) = db`. `non_core_empty(db)` holds. **QED.**
- **Step (`n = S n'`):** `full_iter_n(S n', db) = full_iter(full_iter_n(n', db))`. By IH, `non_core_empty(full_iter_n(n', db))`. By `full_iter_preserves_invariant`, `non_core_empty(full_iter(full_iter_n(n', db)))`. **QED.**

### 5.4 S3: Fixpoint Restriction Equivalence

**Theorem (S3a: step_equivalence).**

> `∀ db, non_core_empty(db) → ∀ c,`
> `  (if is_core(c) then full_step(db, c) else []) =`
> `  (if is_core(c) then core_step(db, c) else [])`

**Proof.** Case split on `is_core(c)`:
- **Core:** `full_step(db, c) = core_step(db, c)` by S2. **QED.**
- **Non-core:** Both sides are `[]`. **QED.**

---

**Theorem (S3b: iter_equivalence).**

> `∀ db, non_core_empty(db) → full_iter(db) = core_iter(db)`

**Proof.** Unfold `full_iter` and `core_iter`. Apply `merge_ext`. For each category `c`:
- **Core:** `full_step(db, c) = core_step(db, c)` by S2.
- **Non-core:** `full_step(db, c) = []` by S1. The core iter already uses `[]` for non-core. **QED.**

---

**Theorem (S3c: fixpoint_restriction).**

> `∀ n db, non_core_empty(db) → full_iter_n(n, db) = core_iter_n(n, db)`

**Proof.** Induction on `n`:

- **Base (`n = 0`):** Both sides equal `db`. **QED.**

- **Step (`n = S n'`):**

  ```
  full_iter_n(S n', db) = full_iter(full_iter_n(n', db))
  core_iter_n(S n', db) = core_iter(core_iter_n(n', db))
  ```

  By IH (with `non_core_empty(db)`):
  `full_iter_n(n', db) = core_iter_n(n', db)`.

  So: `full_iter(full_iter_n(n', db)) = full_iter(core_iter_n(n', db))`

  We need `non_core_empty(core_iter_n(n', db))` to apply S3b.

  Rewrite: `core_iter_n(n', db) = full_iter_n(n', db)` (by IH, reversed).

  By `full_iter_n_preserves_invariant`, `non_core_empty(full_iter_n(n', db))`.

  Therefore `non_core_empty(core_iter_n(n', db))`.

  Apply S3b: `full_iter(core_iter_n(n', db)) = core_iter(core_iter_n(n', db))`. **QED.**

## 6. Invariant Preservation Chain

The invariant `non_core_empty` is the central proof obligation. It forms a chain:

```
db₀ ──[non_core_empty]──> db₁ ──[non_core_empty]──> db₂ ──[non_core_empty]──> ... ──> db_fix
  │                         │                         │
  │  full_iter              │  full_iter              │  full_iter
  │                         │                         │
  └── S1: non-core = []     └── S1: non-core = []     └── S1: non-core = []
      S2: core same              S2: core same              S2: core same
```

**Base case:** The seed database has `non_core_empty` because the input term belongs to a core category (the dispatcher routes it there) and only that category's relation is seeded.

**Inductive step:** Each `full_iter` preserves the invariant by S1 (non-core targets derive nothing) and `merge_preserves_noncore_empty`.

## 7. Example: RhoCalc SCC Analysis

### 7.1 Category Graph (annotated with core/non-core)

```
          ┌─────────────────────────────────────────┐
          │              CORE                       │
          │                                         │
          │   ┌───────┐          ┌───────┐          │
          │   │ Proc  │ <------> │ Name  │          │
          │   │ (prim)│          │       │          │
          │   └───────┘          └───────┘          │
          │       ↑↑                  ↑             │
          └───────┼┼──────────────────┼─────────────┘
                  ││                  │
          ┌───────┼┼──────────────────┼─────────────┐
          │       ││  NON-CORE        │             │
          │       ││                  │             │
          │   ┌───┘│──────┐    ┌──────┘──┐          │
          │   │ Expr      │    │ Chan    │          │
          │   │ →Proc,Name│    │ →Name   │          │
          │   │ →Expr,Grnd│    └─────────┘          │
          │   └───────────┘                         │
          │                                         │
          │   ┌─────────┐    ┌───────┐              │
          │   │ Ground  │    │ Float │              │
          │   │ (leaf)  │    │ (leaf)│              │
          │   └─────────┘    └───────┘              │
          └─────────────────────────────────────────┘
```

### 7.2 Proven Properties

| Lemma | Statement | File |
|-------|-----------|------|
| `rho_Proc_reaches_Name` | `reach(Proc, Name)` | `ConcreteInstantiations.v:224-229` |
| `rho_Name_reaches_Proc` | `reach(Name, Proc)` | `ConcreteInstantiations.v:231-236` |
| `rho_Proc_is_core` | `bidi_reach(Proc, Proc)` | `ConcreteInstantiations.v:239-240` |
| `rho_Name_is_core` | `bidi_reach(Proc, Name)` | `ConcreteInstantiations.v:243-248` |
| `rho_Proc_reach_only_Proc_Name` | `reach(Proc, tgt) → tgt ∈ {Proc, Name}` | `ConcreteInstantiations.v:279-293` |
| `rho_Proc_not_reach_Expr` | `¬reach(Proc, Expr)` | `ConcreteInstantiations.v:296-300` |
| `rho_Expr_not_core` | `¬bidi_reach(Proc, Expr)` | `ConcreteInstantiations.v:303-307` |
| `rho_Chan_not_core` | `¬bidi_reach(Proc, Chan)` | `ConcreteInstantiations.v:310-315` |
| `rho_Ground_not_core` | `¬bidi_reach(Proc, Ground)` | `ConcreteInstantiations.v:317-322` |
| `rho_Float_not_core` | `¬bidi_reach(Proc, Float)` | `ConcreteInstantiations.v:324-329` |

### 7.3 Closure Argument

The proof that `Proc` can only reach `{Proc, Name}` proceeds by:

1. **Edge closure** (`rho_Proc_Name_closed`): If `src ∈ {Proc, Name}` and `edge(src, tgt)`, then `tgt ∈ {Proc, Name}`. Proved by inversion on `rho_edge`.

2. **Inductive generalization** (`rho_Proc_reach_only_Proc_Name`): By induction on `reach`:
   - **Base (reach_refl):** `Proc ∈ {Proc, Name}`. **QED.**
   - **Step (reach_step a b c):** `edge(a, b)` and `reach(b, c)` with `a ∈ {Proc, Name}` (from outer induction hypothesis). By closure, `b ∈ {Proc, Name}`. By IH, `c ∈ {Proc, Name}`. **QED.**

## 8. Relationship to Opt 3

The hypothesis `derive_unreachable_empty` in SCC splitting follows directly from Opt 3 (Dead Rule Pruning). The two optimizations are complementary:

- **Opt 3** prunes rules for unreachable `(src, tgt)` pairs at code generation time
- **Opt 5** exploits the fact that non-core relations stay empty at runtime

The invariant `non_core_empty` is the runtime analog of the compile-time reachability analysis. Both rely on the same underlying graph structure.

## 9. Spec-to-Code Traceability

| Rocq Definition | Rust / Ascent Code | Location |
|-----------------|-------------------|----------|
| `is_core` | `compute_core_categories` | `common.rs:357-391` |
| `core_cats` | `BTreeSet` from `compute_core_categories` | `common.rs:369-383` |
| `full_step` | full Ascent struct fixpoint step | `language.rs:1275-1286` |
| `core_step` | core Ascent struct fixpoint step | `language.rs:1262-1272` |
| `derive` | consolidated subterm extraction | `categories.rs:50-53` |
| `run_ascent_typed` | dispatcher: core vs full struct | `language.rs:1356-1366` |
| `non_core_empty` | invariant (by construction: core inputs seed only core relations) | `language.rs:1262-1272` (core dispatch seeds only core categories) |
| `S1_non_core_derives_nothing` | — | `SCCSplitting.v:166-181` |
| `S2_core_derivations_equal` | — | `SCCSplitting.v:187-203` |
| `S3_fixpoint_restriction` | — | `SCCSplitting.v:344-360` |
| `full_iter_preserves_invariant` | — | `SCCSplitting.v:249-260` |
| `full_iter_n_preserves_invariant` | — | `SCCSplitting.v:263-275` |

## 10. Rocq Source Reference

- **Files:**
  - `formal/rocq/ascent_optimizations/theories/GraphReachability.v` (156 lines) — graph model, reachability
  - `formal/rocq/ascent_optimizations/theories/SCCSplitting.v` (362 lines) — main theorems
  - `formal/rocq/ascent_optimizations/theories/ConcreteInstantiations.v` (385 lines) — RhoCalc instance
- **Dependencies:** `SCCSplitting.v` depends on `Prelude.v` and `GraphReachability.v`
- **Key constructs:** `is_core`, `core_cats`, `non_core_empty`, `full_step`, `core_step`, `full_iter`, `core_iter`, `full_iter_n`, `core_iter_n`, `S1_non_core_derives_nothing`, `S2_core_derivations_equal`, `S3_step_equivalence`, `S3_iter_equivalence`, `S3_fixpoint_restriction`, `full_iter_preserves_invariant`, `full_iter_n_preserves_invariant`
