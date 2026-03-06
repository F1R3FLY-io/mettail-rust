# Programmatic LanguageSpec Composition

## Intuition

`compose_languages()` is the API for tooling, testing, and dynamic grammar
combination. Unlike the macro-level mechanisms (`extends:`/`includes:`/`mixins:`),
the LanguageSpec API operates on already-classified grammar specifications and
produces a merged spec ready for `generate_parser()`.

## Why Important

- **Test infrastructure**: combine grammar specs programmatically in unit tests
- **IDE tooling**: merge grammars dynamically for completion/diagnostics
- **Dynamic composition**: build grammars from configuration files or user input

## API Walkthrough

**Core functions** (all in `prattail/src/compose.rs`):

```rust
pub fn compose_languages(
    spec_a: &LanguageSpec,
    spec_b: &LanguageSpec,
) -> Result<LanguageSpec, Vec<CompositionError>>
```

Merges two specs. Grammar A has priority (primary category, native types).

```rust
pub fn compose_many(
    specs: &[&LanguageSpec],
) -> Result<LanguageSpec, Vec<CompositionError>>
```

Left fold: `compose(A, B)` then `compose(AB, C)` and so on. Grammar A has
highest priority. Edge case: empty slice returns an empty spec named `"empty"`.

```rust
pub fn compose_with_wfst(
    spec_a: &LanguageSpec,
    spec_b: &LanguageSpec,
    wfsts_a: &BTreeMap<String, PredictionWfst>,
    wfsts_b: &BTreeMap<String, PredictionWfst>,
    terminals_a: &BTreeSet<String>,
    terminals_b: &BTreeSet<String>,
) -> Result<WfstCompositionResult, Vec<CompositionError>>
```

Merges specs AND prediction WFSTs in a single operation.

## WFST-Aware Composition

When composing grammars that already have constructed WFSTs,
`compose_with_wfst()` avoids full WFST reconstruction:

1. Calls `compose_languages()` to merge the specs
2. Merges prediction WFSTs: shared categories use `PredictionWfst::union()`,
   unique categories move directly
3. Merges terminal sets: `BTreeSet` union
4. Computes `WfstCompositionSummary`

```rust
pub struct WfstCompositionResult {
    pub spec: LanguageSpec,
    pub prediction_wfsts: BTreeMap<String, PredictionWfst>,
    pub terminals: BTreeSet<String>,
    pub summary: WfstCompositionSummary,
}

pub struct WfstCompositionSummary {
    pub base: CompositionSummary,
    pub wfst_count: usize,
    pub wfsts_merged: usize,
    pub total_actions: usize,
    pub total_states: usize,
}
```

## `CompositionError` Variants

| Variant                      | Condition                               | Fields                                       |
|------------------------------|-----------------------------------------|----------------------------------------------|
| `CategoryNativeTypeMismatch` | Shared category, different native types | `category`, `native_type_a`, `native_type_b` |
| `DuplicateRuleLabel`         | Same constructor label in both          | `label`, `category_a`, `category_b`          |
| `InvalidCategoryReference`   | Rule references unknown category        | `rule_label`, `referenced_category`          |
| `AssociativityConflict`      | Same infix operator, different assoc    | `terminal`, `category`, `assoc_a`, `assoc_b` |
| `BindingPowerConflict`       | Same prefix operator, different BP      | `terminal`, `category`, `bp_a`, `bp_b`       |

All errors are collected and returned together (no early exit).

## `CompositionSummary`

```rust
pub struct CompositionSummary {
    pub merged_name: String,
    pub categories_a: usize,
    pub categories_b: usize,
    pub categories_merged: usize,
    pub rules_a: usize,
    pub rules_b: usize,
    pub shared_categories: Vec<String>,
}
```

Display: `Composed 'A_B': 3 categories (2 from A, 2 from B, 1 shared), 6 rules (3 + 3)`

## Correctness Guarantees

The composition maintains these invariants (see `theory/wfst/composition-correctness.md`):

- **Union completeness**: merged grammar accepts any input that either source accepts
- **Soundness**: merged grammar does not accept inputs rejected by both sources
- **Weight preservation**: WFST weights from source grammars are preserved in union
- **Dispatch determinism**: the merged grammar's dispatch tables are deterministic
  for all tokens in the merged FIRST sets

## Example

```rust
use prattail::compose::{compose_languages, composition_summary};

let merged = compose_languages(&calc_spec, &logic_spec)
    .expect("no conflicts");

let summary = composition_summary(&calc_spec, &logic_spec, &merged);
println!("{}", summary);

let parser_code = generate_parser(&merged);
```

## Incremental FIRST/FOLLOW Sets

For runtime composition, incremental helpers avoid full recomputation:

- `incremental_first_sets(existing, new_rules, new_categories)` -- extends
  existing FIRST sets
- `incremental_follow_sets(existing, new_inputs, new_categories, first_sets)` --
  extends FOLLOW sets
- `merge_terminal_sets(a, b)` -- BTreeSet union

## PredictionWfst::union

Merges another WFST into `self`:

1. Maps `other`'s token names into `self`'s namespace
2. Appends `other`'s actions with adjusted indices
3. Imports `other`'s start-state transitions into `self`'s start state
4. Preserves beam width and category name

## Source Reference

| Symbol                   | Location                     |
|--------------------------|------------------------------|
| `compose_languages`      | `prattail/src/compose.rs`    |
| `compose_many`           | `prattail/src/compose.rs`    |
| `compose_with_wfst`      | `prattail/src/compose.rs`    |
| `composition_summary`    | `prattail/src/compose.rs`    |
| `CompositionError`       | `prattail/src/compose.rs`    |
| `incremental_first_sets` | `prattail/src/prediction.rs` |
| `PredictionWfst::union`  | `prattail/src/wfst.rs`       |

Test count: 19 tests (13 core + 6 WFST composition).
