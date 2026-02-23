# Grammar Composition

**Feature gate:** `wfst`

**Date:** 2026-02-22

Grammar composition combines two independently defined `LanguageSpec` values
into a single merged specification that accepts inputs from either source
grammar. The merged specification is then passed to `generate_parser()` through
the normal PraTTaIL pipeline — composition is a preprocessing step, not a
parallel parsing mode.

The operation is analogous to WFST union: two automata that recognize
disjoint languages are merged into one that recognizes the union. PraTTaIL
grammars operate at the level of categories and rules rather than states and
transitions, so the merge algorithm works structurally:

1. Categories are merged by name union, with the first grammar's `native_type`
   taking priority for shared categories.
2. Rules are concatenated with the first grammar's rules appearing first.
3. Invariants are checked: native type matches, label uniqueness, category
   references, associativity consistency.
4. All rules are reclassified in the merged grammar (cast detection, infix
   detection, etc.).

---

## Table of Contents

1. [Language Union Semantics](#1-language-union-semantics)
2. [compose\_languages Algorithm](#2-compose_languages-algorithm)
3. [Category Merging](#3-category-merging)
4. [Rule Merging](#4-rule-merging)
5. [Validation and Error Variants](#5-validation-and-error-variants)
6. [compose\_many](#6-compose_many)
7. [composition\_summary](#7-composition_summary)
8. [Diagrams](#8-diagrams)
9. [Example: Calculator + BooleanLogic](#9-example-calculator--booleanlogic)
10. [WFST-Aware Composition](#10-wfst-aware-composition)
11. [Source Reference](#11-source-reference)

---

## 1. Language Union Semantics

A grammar in PraTTaIL defines:
- A set of *categories* (typed non-terminals, each with an optional Rust type).
- A set of *rules* (productions associating a constructor label, a category,
  and a syntax pattern).

Two grammars are *composable* if their rules define non-overlapping
constructor labels and their shared categories use the same Rust native type.
When both conditions hold, the merged grammar accepts any input that either
source grammar would accept, with the first grammar's categories and primary
designation taking precedence.

**Grammar A priority.** When both grammars share a category name, grammar A's
`native_type` is used in the merged grammar. Grammar A's primary category
(if any) becomes the primary of the merged grammar; grammar B's primary is
demoted to non-primary. This matches the intended usage pattern of
"base grammar + extension": the base grammar defines the primary category
and core types.

---

## 2. compose\_languages Algorithm

`compose_languages(spec_a, spec_b) → Result<LanguageSpec, Vec<CompositionError>>`

All validation errors are collected into a `Vec<CompositionError>` before
returning. This means multiple errors are reported in one call rather than
failing on the first.

```
Step 1: merge_categories(spec_a.types, spec_b.types)
    ─ accumulate by name; A-priority for native_type
    ─ error: CategoryNativeTypeMismatch if shared category has different native_type

Step 2: merge_rules(spec_a, spec_b)
    ─ A rules first, then B rules
    ─ error: DuplicateRuleLabel if any label appears in both

Step 3: validate_category_refs(all merged rules)
    ─ check every NonTerminal, Binder, Collection, ZipMapSep category reference
    ─ error: InvalidCategoryReference if referenced category not in merged types

Step 4: check_associativity_conflicts(spec_a, spec_b)
    ─ for each (terminal, category) pair appearing as infix in both:
    ─ error: AssociativityConflict if associativity differs

Step 5: if any errors → return Err(errors)

Step 6: check_binding_power_conflicts(spec_a, spec_b)
    ─ for each (terminal, category) pair with explicit prefix_precedence in both:
    ─ error: BindingPowerConflict if precedence values differ

Step 7: LanguageSpec::new(merged_name, merged_types, merged_inputs)
    ─ reclassifies all rules via classify_rule()
    ─ merged_name = "A_B" (concatenation of grammar names)
```

The reclassification in step 7 re-derives all flags that the pipeline
computes from rule structure: `is_infix`, `is_cast`, `is_collection`,
`cast_source_category`, etc. This is important because a rule that was a
cast in grammar B might become a non-cast in the merged grammar if the
referenced category changes its position in the type hierarchy.

---

## 3. Category Merging

`merge_categories` iterates the two category lists and produces a merged
`Vec<CategorySpec>`:

- All categories from grammar A are added first in their original order.
- For each category from grammar B:
  - If the name already exists (from A): verify `native_type` matches. No
    duplication — the A-side version is kept.
  - If the name is new: append it to the merged list.

The `is_primary` flag is handled with a `seen_primary` sentinel: the first
primary category encountered across A then B becomes the primary of the merged
grammar. All subsequent categories with `is_primary = true` are demoted.
This is intentionally not an error — the rationale is given in the source:

> `MultiplePrimaryCategories` is intentionally NOT an error. When two grammars
> both declare a primary, `merge_categories()` keeps the first grammar's primary
> and demotes the second. This matches the intuition that "base grammar defines
> the primary category."

---

## 4. Rule Merging

`merge_rules` converts each `RuleSpec` in both grammars to a `RuleSpecInput`
(the unclassified input form) and concatenates them. Grammar A's rules appear
first, preserving the base grammar's binding-power ordering.

Label uniqueness is enforced: if a label appears in both grammars, a
`DuplicateRuleLabel` error is emitted. The duplicate rule is still added to
the merged list (for completeness during error reporting) but the merge
will be rejected in step 5.

---

## 5. Validation and Error Variants

| Error Variant                | Condition                                                                             | Fields                                       |
|------------------------------|---------------------------------------------------------------------------------------|----------------------------------------------|
| `CategoryNativeTypeMismatch` | Two categories share a name but differ in `native_type`                               | `category`, `native_type_a`, `native_type_b` |
| `DuplicateRuleLabel`         | Same constructor label in both grammars                                               | `label`, `category_a`, `category_b`          |
| `InvalidCategoryReference`   | A rule references a category not in the merged type set                               | `rule_label`, `referenced_category`          |
| `AssociativityConflict`      | Same infix `(terminal, category)` has conflicting associativity                       | `terminal`, `category`, `assoc_a`, `assoc_b` |
| `BindingPowerConflict`       | Same unary-prefix `(terminal, category)` has conflicting explicit `prefix_precedence` | `terminal`, `category`, `bp_a`, `bp_b`       |

`CompositionError` implements `Display` (human-readable message) and
`std::error::Error`. All five variants are covered by `fmt::Display`.

**Note on `InvalidCategoryReference`.** This error can arise when grammar B
has a rule that references a category defined only in grammar B, and that
category's name collides with a different category in grammar A causing a
`CategoryNativeTypeMismatch`. In that case, both errors will be reported.
The grammar author must resolve both.

---

## 6. compose\_many

`compose_many(specs: &[&LanguageSpec]) → Result<LanguageSpec, Vec<CompositionError>>`

Folds left: `compose(A, B)` → `compose(AB, C)` → … This means grammar A
has highest priority, followed by B, followed by C.

If any pairwise composition fails, `compose_many` propagates the error
immediately without attempting further compositions.

Edge case: `compose_many(&[])` returns an empty `LanguageSpec` with name
`"empty"` and no categories or rules. This is the identity element for
composition.

---

## 7. composition\_summary

`composition_summary(spec_a, spec_b, merged) → CompositionSummary`

A non-failing diagnostic query that returns counts and the list of shared
category names. This is useful for logging and user-facing diagnostics without
re-running the full composition pipeline.

```rust
pub struct CompositionSummary {
    pub merged_name: String,
    pub categories_a: usize,
    pub categories_b: usize,
    pub categories_merged: usize,   // ≤ categories_a + categories_b
    pub rules_a: usize,
    pub rules_b: usize,
    pub shared_categories: Vec<String>,
}
```

`Display` for `CompositionSummary` produces:

```
Composed 'A_B': 3 categories (2 from A, 2 from B, 1 shared), 2 rules (1 + 1)
```

---

## 8. Diagrams

### 8.1 Merge Steps

```
  ┌─────────────────────┐      ┌─────────────────────┐
  │   Grammar A         │      │   Grammar B         │
  │                     │      │                     │
  │  categories:        │      │  categories:        │
  │    Expr {Int} ●     │      │    Expr {Bool} ●    │  ← mismatch!
  │                     │      │    Val  {Int}       │
  │  rules:             │      │  rules:             │
  │    Add, Mul, Num    │      │    And, Or, True    │
  └─────────────────────┘      └─────────────────────┘
             │                          │
             └──────────┬───────────────┘
                        ▼
          compose_languages(A, B)
                        │
          ┌─────────────┼─────────────────┐
          │             │                 │
          ▼             ▼                 ▼
    merge_categories  merge_rules    validate
          │
          ▼
    ERROR: CategoryNativeTypeMismatch
    category = "Expr", native_type_a = Some("Int"),
                        native_type_b = Some("Bool")
```

The fix: grammar B should use a distinct category name.

```
  ┌─────────────────────┐      ┌─────────────────────┐
  │   Grammar A (Calc)  │      │   Grammar B (Logic) │
  │                     │      │                     │
  │  categories:        │      │  categories:        │
  │    Expr {Int} ●     │      │    BoolExpr {Bool} ●│
  │                     │      │                     │
  │  rules:             │      │  rules:             │
  │    Add, Mul, Num    │      │    And, Or, True    │
  └─────────────────────┘      └─────────────────────┘
             │                          │
             └──────────┬───────────────┘
                        ▼
          compose_languages(A, B)
                        │
          merged grammar "Calc_Logic":
          ┌─────────────▼──────────────────────┐
          │  categories:                       │
          │    Expr     {Int}  is_primary=true │  ← from A
          │    BoolExpr {Bool} is_primary=false│  ← from B (demoted)
          │                                    │
          │  rules (A first, then B):          │
          │    Add, Mul, Num                   │
          │    And, Or, True                   │
          └────────────────────────────────────┘
```

### 8.2 Composition Data-Flow

```
  spec_a ──────────────────────────────────────────┐
                                                   │
  spec_b ──────────────────────────────────────────┤
                                                   │
                                                   ▼
                                  compose_languages(a, b)
                                          │
              ┌───────────────────────────┼────────────────────────┐
              │                           │                        │
              ▼                           ▼                        ▼
      merge_categories            merge_rules              validate refs
      (name → CategorySpec)       (label collision)        + associativity
              │                           │                        │
              └───────────────────────────┼────────────────────────┘
                                          │
                                   errors? ─── yes ──► Err(Vec<CompositionError>)
                                          │ no
                                          ▼
                                 LanguageSpec::new(
                                   name = "A_B",
                                   types = merged_types,
                                   rules = merged_inputs   ← reclassified
                                 )
                                          │
                                          ▼
                                  generate_parser()
                                  (normal pipeline)
```

---

## 9. Example: Calculator + BooleanLogic

Two grammars: a calculator grammar with integer expressions, and a boolean
logic grammar. They use different categories so there is no type conflict.

**Grammar A (Calculator):**

```rust
// categories: Int { i32 } (primary)
// rules:
//   NumLit: Int → "0"
//   Add:    Int → Int "+" Int
//   Mul:    Int → Int "*" Int
```

**Grammar B (BoolLogic):**

```rust
// categories: BoolExpr { bool } (primary — will be demoted)
// rules:
//   TrueLit: BoolExpr → "true"
//   And:     BoolExpr → BoolExpr "&&" BoolExpr
//   Or:      BoolExpr → BoolExpr "||" BoolExpr
```

**Composition:**

```rust
use prattail::compose::compose_languages;

let merged = compose_languages(&calc_spec, &logic_spec)
    .expect("no conflicts between Calculator and BoolLogic");

// merged.name = "Calculator_BoolLogic"
// merged.types = [Int {i32, primary=true}, BoolExpr {bool, primary=false}]
// merged.rules = [NumLit, Add, Mul, TrueLit, And, Or]

// The merged grammar can parse both "1 + 2 * 3" and "true && false"
// Primary category is Int (from Calculator).
```

**Checking the summary:**

```rust
use prattail::compose::composition_summary;

let summary = composition_summary(&calc_spec, &logic_spec, &merged);
println!("{}", summary);
// → Composed 'Calculator_BoolLogic': 2 categories (1 from A, 1 from B, 0 shared), 6 rules (3 + 3)
```

**Cross-category extension (rules that span both grammars):**

If you want `BoolExpr` rules that compare `Int` values:

```rust
// Grammar C: comparison operators
// categories: BoolExpr { bool } (shared with B)
// rules:
//   Eq: BoolExpr → Int "==" Int   (cross-category: Int in BoolExpr rule)
//   Lt: BoolExpr → Int "<"  Int
```

This composes cleanly with the `A_B` merged grammar because `Int` exists in
the merged type set, so the `InvalidCategoryReference` validation passes.

```rust
let merged_abc = compose_many(&[&calc_spec, &logic_spec, &cmp_spec])
    .expect("three-grammar composition");
// merged_abc.types = [Int, BoolExpr]  (BoolExpr shared between B and C)
// merged_abc.rules = [NumLit, Add, Mul, TrueLit, And, Or, Eq, Lt]
```

---

## 10. WFST-Aware Composition

**Feature gate:** `wfst`

When the `wfst` feature is active, grammar composition gains additional
capabilities: prediction WFST merging, incremental FIRST/FOLLOW set
computation, and binding-power conflict detection.

### 10.1 compose\_with\_wfst

`compose_with_wfst(spec_a, spec_b, wfsts_a, wfsts_b, terminals_a, terminals_b)
→ Result<WfstCompositionResult, Vec<CompositionError>>`

This function combines two grammar specs AND their prediction WFSTs in a
single operation:

1. Calls `compose_languages()` to merge the specs (including BP conflict check).
2. Merges prediction WFSTs: for shared categories, grammar A's WFST absorbs
   grammar B's via `PredictionWfst::union()`. For categories unique to B,
   the WFST is moved to the result directly.
3. Merges terminal sets via `merge_terminal_sets()`.
4. Computes an enriched `WfstCompositionSummary` that extends `CompositionSummary`
   with WFST-specific counts.

```rust
pub struct WfstCompositionResult {
    pub spec: LanguageSpec,
    pub prediction_wfsts: BTreeMap<String, PredictionWfst>,
    pub terminals: BTreeSet<String>,
    pub summary: WfstCompositionSummary,
}

pub struct WfstCompositionSummary {
    pub base: CompositionSummary,
    pub wfst_count: usize,       // total WFSTs in result
    pub wfsts_merged: usize,     // WFSTs merged via union (shared categories)
    pub total_actions: usize,    // sum of actions across all WFSTs
    pub total_states: usize,     // sum of states across all WFSTs
}
```

### 10.2 Incremental FIRST/FOLLOW

When composing grammars at runtime, the incremental helpers avoid full
FIRST/FOLLOW recomputation:

- `incremental_first_sets(existing, new_rules, new_categories)` — extends
  existing FIRST sets with tokens contributed by new rules. Runs fixed-point
  iteration over new rules only; existing categories are stable.
- `incremental_follow_sets(existing, new_inputs, new_categories, first_sets)` —
  extends existing FOLLOW sets using new rule inputs.
- `merge_terminal_sets(a, b)` — BTreeSet union.

These are defined in `prattail/src/prediction.rs` under `#[cfg(feature = "wfst")]`.

### 10.3 PredictionWfst::union

`PredictionWfst::union(&mut self, other: &PredictionWfst)` merges another
WFST into `self` via weighted union:

1. Builds a token-name → token-ID mapping from `other` into `self`'s namespace.
2. Appends `other`'s actions (with offset-adjusted indices) to `self`.
3. Imports `other`'s start-state transitions into `self`'s start state,
   creating new final states for each imported transition.
4. Preserves `self`'s beam width and category name.

### 10.4 Binding-Power Reconciliation

`check_binding_power_conflicts()` scans both grammars for unary-prefix rules
with explicit `prefix_precedence`. If the same `(terminal, category)` pair
appears in both grammars with different precedence values, a
`BindingPowerConflict` error is emitted.

Only rules with **explicit** `prefix_precedence` are checked. Auto-computed
binding powers (the majority) are not compared, because they will be
recomputed by `LanguageSpec::new()` during reclassification.

---

## 11. Source Reference

| Symbol                                    | Location                     |
|-------------------------------------------|------------------------------|
| `compose_languages`                       | `prattail/src/compose.rs`    |
| `compose_many`                            | `prattail/src/compose.rs`    |
| `compose_with_wfst`                       | `prattail/src/compose.rs`    |
| `composition_summary`                     | `prattail/src/compose.rs`    |
| `CompositionError`                        | `prattail/src/compose.rs`    |
| `CompositionError::BindingPowerConflict`  | `prattail/src/compose.rs`    |
| `CompositionSummary`                      | `prattail/src/compose.rs`    |
| `WfstCompositionResult`                   | `prattail/src/compose.rs`    |
| `WfstCompositionSummary`                  | `prattail/src/compose.rs`    |
| `check_binding_power_conflicts` (private) | `prattail/src/compose.rs`    |
| `merge_categories` (private)              | `prattail/src/compose.rs`    |
| `merge_rules` (private)                   | `prattail/src/compose.rs`    |
| `validate_category_refs` (private)        | `prattail/src/compose.rs`    |
| `check_associativity_conflicts` (private) | `prattail/src/compose.rs`    |
| `incremental_first_sets`                  | `prattail/src/prediction.rs` |
| `incremental_follow_sets`                 | `prattail/src/prediction.rs` |
| `merge_terminal_sets`                     | `prattail/src/prediction.rs` |
| `PredictionWfst::union`                   | `prattail/src/wfst.rs`       |

Test count: 19 (in `prattail/src/compose.rs` `#[cfg(test)]` module; 13 core + 6 WFST-gated).

See also:
- [../README.md](../README.md) — WFST subsystem overview and feature tiers
- [prediction.md](prediction.md) — after composition, each merged category gets a prediction WFST
- [../../../design/architecture-overview.md](../../../design/architecture-overview.md) — PraTTaIL pipeline where `generate_parser()` is called
