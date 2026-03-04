# Runtime Delegation (`compose_languages!`)

## Intuition

`compose_languages!` wraps independently compiled languages behind a single
interface — no re-compilation needed. Unlike merge-based composition
(`extends:`/`includes:`/`mixins:`), delegation keeps each sub-language's parser
and Ascent program intact. The wrapper tries each in declaration order and
delegates all operations to the matching sub-language.

## Why Important

- **Maximum modularity**: each language is developed and tested independently.
- **Independent compilation**: changing one sub-language does not recompile
  others.
- **Late binding**: sub-languages are combined at the API boundary, not at the
  grammar level.

## Fundamental Difference from Merge-Based Composition

```
  Merge-based (extends/includes/mixins):        Delegation (compose_languages!):
  ┌──────────┐  ┌──────────┐                    ┌──────────┐  ┌──────────┐
  │ Grammar A│  │ Grammar B│                    │ Lang A   │  │ Lang B   │
  └────┬─────┘  └────┬─────┘                    │ (parser) │  │ (parser) │
       │             │                          │ (ascent) │  │ (ascent) │
       └──────┬──────┘                          └────┬─────┘  └────┬─────┘
              │                                      │             │
              ▼                                      └──────┬──────┘
     ┌──────────────┐                                       │
     │ Merged Grammar│                                      ▼
     │ (single parse)│                              ┌──────────────┐
     └──────┬───────┘                               │ Wrapper      │
            │                                       │ try A → try B│
            ▼                                       └──────┬───────┘
     ┌──────────────┐                                      │
     │ Single Parser │                                     ▼
     │ Single Ascent │                              ┌──────────────┐
     └──────────────┘                               │ Delegation   │
                                                    │ (N parsers)  │
                                                    └──────────────┘
```

## Syntax

```rust
compose_languages! {
    name: CalcLambda,
    languages: [
        crate::calculator::Calculator,
        crate::lambda::Lambda,
    ],
}
```

## Generated Types

The macro generates five types:

### `CalcLambdaTermInner` enum

```rust
enum CalcLambdaTermInner {
    Calculator(CalculatorTerm),
    Lambda(LambdaTerm),
}
```

### `CalcLambdaTerm` wrapper struct

- Implements `mettail_runtime::Term`.
- Provides downcast accessors: `as_calculator() -> Option<&CalculatorTerm>`,
  `as_lambda() -> Option<&LambdaTerm>`.
- Hash includes discriminant + inner term ID.

### `CalcLambdaEnv` struct

- Contains per-sub-language environment:
  `calculator_env: Box<dyn Any + Send + Sync>`,
  `lambda_env: Box<dyn Any + Send + Sync>`.
- Methods: `new()`, `clear()`, `is_empty()`.

### `CalcLambdaMetadata` struct

- Lazily aggregates metadata from all sub-languages via `OnceLock`.
- Methods return `&'static` slices: `types()`, `terms()`, `equations()`,
  `rewrites()`.

### `CalcLambdaLanguage` struct

- Zero-sized struct implementing `mettail_runtime::Language`.
- All methods delegate to sub-languages.

## Parsing Strategy

```
parse_term(input):
    errors = []
    for sub_lang in [Calculator, Lambda]:    // declaration order
        match sub_lang.parse_term(input):
            Ok(term) → return Ok(CalcLambdaTerm(sub_lang_variant(term)))
            Err(e) → errors.push(e)
    return Err(format!("No sub-language could parse: {errors}"))
```

First successful parse wins. If all sub-languages fail, errors from all
attempts are aggregated.

## Method Dispatch

| Method Category | Strategy |
|----------------|----------|
| `parse_term()` | Sequential try-each, first success wins |
| `run_ascent()`, `try_direct_eval()`, `normalize_term()` | Match on variant, delegate to owning sub-language |
| `add_to_env()`, `substitute_env()` | Route to correct sub-env based on term variant |
| `remove_from_env()` | Try all sub-envs until success |
| `list_env()` | Aggregate from all sub-envs |
| `is_env_empty()` | All sub-envs must be empty |

## Downcast Accessors

```rust
let result = CalcLambda.parse_term("1 + 2")?;
if let Some(calc_term) = result.as_calculator() {
    // Use Calculator-specific API
}
```

## End-to-End Example

From `languages/src/composition/composed_lang.rs`:

```rust
compose_languages! {
    name: CalcLambda,
    languages: [crate::calculator::Calculator, crate::lambda::Lambda],
}
```

- `CalcLambda.parse_term("1 + 2")` tries Calculator first, succeeds, and
  returns `CalcLambdaTerm(Calculator(...))`.
- `CalcLambda.parse_term("^x.{x}")` tries Calculator, fails, then tries
  Lambda, succeeds, and returns `CalcLambdaTerm(Lambda(...))`.

## Integration

Each sub-language has its own independently compiled parser and Ascent program.
Composition happens ONLY at the API boundary — the `Language` trait methods are
delegated, never merged.

## When to Use

- Sub-languages are independently developed and tested.
- You want to avoid recompilation when one grammar changes.
- The sub-languages have disjoint concrete syntax (no shared operators).
- You need a unified API over heterogeneous grammars.

## When NOT to Use

- Sub-languages share operators (e.g., both define `+`) — use `extends:` or
  `includes:` instead.
- You need cross-category dispatch between grammars — delegation cannot do
  this.
- Performance-critical: delegation has overhead from sequential try-each
  parsing.
