# DSL Configuration

The `language!` macro accepts an optional `options { }` block immediately
after the `name:` field. Every key in the block maps to a field on the
`LanguageSpec` struct that the `prattail_bridge` constructs before calling
`generate_parser()`. Omitting the block entirely is equivalent to specifying
all options at their defaults.

```rust
language! {
    name: MyLang,
    options {
        beam_width: 1.5,
        dispatch: "weighted",
        log_semiring_model_path: "path/to/model.json",
    }
    // ... types, terms, equations, rewrites, logic
}
```

---

## 1. Option: `beam_width`

Controls how aggressively the WFST prediction and recovery stages prune
low-probability alternatives. Requires the `wfst` feature; has no effect
without it.

### 1.1 Syntax

| DSL value              | Meaning                                          |
|------------------------|--------------------------------------------------|
| `none` or `disabled`   | Pruning disabled (default)                       |
| Float literal (`1.5`)  | Prune actions with weight > best + width         |
| `auto`                 | Use `recommended_beam_width` from trained model  |

### 1.2 Mapping to `BeamWidthConfig`

Defined in `prattail/src/lib.rs`:

```rust
pub enum BeamWidthConfig {
    Disabled,       // no pruning
    Explicit(f64),  // prune when weight > best + value
    Auto,           // resolved from trained model at pipeline time
}
```

The DSL parser in `macros/src/ast/language.rs` (`parse_options`) converts
`AttributeValue` tokens to the enum:

```
none / disabled  →  BeamWidthConfig::Disabled
1.5              →  BeamWidthConfig::Explicit(1.5)
auto             →  BeamWidthConfig::Auto
```

### 1.3 `to_option()` helper

`BeamWidthConfig::to_option()` converts the enum to the `Option<f64>` used
by `predict_pruned()` and `viterbi_recovery_beam()`:

| Variant             | `to_option()` result                           |
|---------------------|------------------------------------------------|
| `Disabled`          | `None` — no pruning applied                    |
| `Explicit(w)`       | `Some(w)` — passed directly to beam functions |
| `Auto`              | `None` — pipeline resolves from model later    |

For `Auto`, the pipeline reads `TrainedModel::recommended_beam_width` from
the JSON file specified in `log_semiring_model_path` and replaces `Auto` with
the corresponding `Explicit(w)` before codegen. If the model file is absent
or carries no recommendation, `Auto` falls back to `Disabled`.

### 1.4 Examples

```rust
// No pruning (default — same as omitting the option)
beam_width: disabled,

// Explicit pruning: drop alternatives more than 1.5 tropical units above best
beam_width: 1.5,

// Automatic: read recommended width from the trained model
// (requires wfst-log and log_semiring_model_path)
beam_width: auto,
```

### 1.5 Choosing a value

A starting-point heuristic: begin with `1.5` for tight grammars (few
ambiguities), `2.5` for looser ones. Use the `recommended_beam_width` field
returned by `TrainingStats` after a training run as a data-driven
alternative. See [usage/training-guide.md](training-guide.md) for the
full training workflow.

---

## 2. Option: `dispatch`

Selects how the parser orders its prefix and cross-category dispatch arms.
The default, `"static"`, uses declaration order; `"weighted"` reorders arms
by WFST probability, trying the highest-probability alternative first.

### 2.1 Syntax

| DSL value    | Meaning                                           |
|--------------|---------------------------------------------------|
| `"static"`   | FIRST-set declaration-order dispatch (default)    |
| `"weighted"` | WFST-weighted dispatch                            |
| `"auto"`     | Resolve from grammar complexity metrics           |

### 2.2 Mapping to `DispatchStrategy`

Defined in `prattail/src/lib.rs`:

```rust
pub enum DispatchStrategy {
    Static,    // default
    Weighted,  // build and use WFSTs
    Auto,      // decide at pipeline time
}
```

### 2.3 `Auto` resolution rules

`DispatchStrategy::resolve(total_rules, cross_category_count, ambiguous_overlap_count)`
evaluates the following conditions at pipeline time:

```
Weighted  when  (total_rules ≥ 30  AND  cross_category_count > 0)
               OR  ambiguous_overlap_count ≥ 3
Static    otherwise
```

When the `wfst` feature is absent, `resolve()` always returns `Static`
regardless of the argument. If `"weighted"` was explicitly specified a
warning is printed to stderr:

```
warning: dispatch: weighted requires --features wfst; falling back to static dispatch
```

### 2.4 When to use each mode

```
Static   — small/medium grammars without cross-category ambiguity;
           zero WFST construction overhead at compile time.

Weighted — large grammars (≥30 rules), multiple overlapping cross-category
           FIRST sets, or grammars where parse order measurably affects
           error message quality.

Auto     — safe default for production grammars; the pipeline decides
           based on the concrete shape of the grammar.
```

---

## 3. Option: `log_semiring_model_path`

A string literal naming a file path to a `TrainedModel` JSON file produced
by the training API. The path is resolved relative to the workspace root at
macro-expansion time (compile time).

### 3.1 Syntax

```rust
log_semiring_model_path: "path/to/model.json",
```

### 3.2 Usage constraints

- Required when `beam_width: auto` is specified. The DSL parser emits a
  compile error if `auto` is used without this option.
- Ignored when `beam_width` is `disabled` or an explicit float (the model
  file is not read).
- Has no effect without the `wfst-log` feature. The pipeline skips model
  loading when `wfst-log` is absent, which means `auto` degrades to
  `disabled` silently in that case.

### 3.3 Model file format

The JSON file is the `TrainedModel` struct serialized by
`TrainedModel::save()`. A minimal valid file:

```json
{
  "rule_weights": {
    "Add": 0.3,
    "Mul": 0.5,
    "Num": 0.1,
    "Var": 0.2
  },
  "recommended_beam_width": 1.5,
  "metadata": {
    "epochs": 100,
    "final_loss": 0.042,
    "converged": true,
    "num_examples": 500,
    "learning_rate": 0.01
  }
}
```

See [usage/training-guide.md](training-guide.md) for how to generate this
file from a training corpus.

---

## 4. `AttributeValue` Variants

The `options { }` block parser (`macros/src/ast/language.rs`) recognises
five value forms, each mapped to an `AttributeValue` variant:

```
Float    — any floating-point literal:    1.5, 2.0, 0.5
Int      — any integer literal:           1, 42
Bool     — true or false
Str      — double-quoted string literal:  "weighted", "path/to/model.json"
Keyword  — bare identifier:              none, disabled, auto
```

Unknown option keys produce a compile-time warning (currently) and are
ignored by the pipeline.

---

## 5. Complete Example

A grammar using all three options:

```rust
language! {
    name: Calculator,
    options {
        beam_width: 1.5,
        dispatch: "weighted",
        log_semiring_model_path: "models/calc_model.json",
    }

    types {
        ![i64] as Expr;
    }

    terms {
        Add(Expr, Expr) : Expr = lhs:Expr "+" rhs:Expr => { lhs + rhs },
        Sub(Expr, Expr) : Expr = lhs:Expr "-" rhs:Expr => { lhs - rhs },
        Mul(Expr, Expr) : Expr = lhs:Expr "*" rhs:Expr => { lhs * rhs },
        Div(Expr, Expr) : Expr = lhs:Expr "/" rhs:Expr => { lhs / rhs },
        Neg(Expr)       : Expr = "-" e:Expr             => { -e },
        Num(i64)        : Expr = n:Integer               => { n },
    }
}
```

---

## 6. Minimal Example (All Defaults)

When none of the WFST options are needed the block can be omitted entirely.
The three options default to:

```
beam_width             →  BeamWidthConfig::Disabled
dispatch               →  DispatchStrategy::Static
log_semiring_model_path→  (none)
```

```rust
language! {
    name: Minimal,

    types {
        ![i64] as Expr;
    }

    terms {
        Num(i64) : Expr = n:Integer => { n },
    }
}
```

---

## 7. Option-Interaction Diagram

The three options interact when `beam_width: auto` is active. The diagram
below shows the resolution path. Dotted verticals (┊) cross the horizontal
feature-gate boundary.

```
  beam_width: auto
       │
       ▼
  is wfst-log enabled?
  ┌────┴────────────────────────────────────────┐
  │ NO                                          │ YES
  ▼                                             ▼
  BeamWidthConfig::Disabled          log_semiring_model_path set?
  (auto degrades silently)           ┌───────────┴───────────────┐
                                     │ NO                        │ YES
                                     ▼                           ▼
                              BeamWidthConfig::Disabled   read model JSON
                              (warning: no model path)         │
                                                               ▼
                                                  recommended_beam_width present?
                                                  ┌──────────┴──────────┐
                                                  │ NO                  │ YES
                                                  ▼                     ▼
                                           Disabled              Explicit(w)
```

---

## 8. Source Locations

| Component                    | File                                          |
|------------------------------|-----------------------------------------------|
| `AttributeValue` enum        | `macros/src/ast/language.rs`                  |
| `parse_options()` function   | `macros/src/ast/language.rs`                  |
| `BeamWidthConfig` enum       | `prattail/src/lib.rs`                         |
| `DispatchStrategy` enum      | `prattail/src/lib.rs`                         |
| `LanguageSpec` struct        | `prattail/src/lib.rs`                         |
| `predict_pruned()`           | `prattail/src/wfst.rs`                        |
| `viterbi_recovery_beam()`    | `prattail/src/recovery.rs`                    |

---

## 9. Cross-References

- [usage/feature-gates.md](feature-gates.md) — enabling `wfst` and `wfst-log` features,
  Cargo.toml snippets for every crate in the chain
- [usage/training-guide.md](training-guide.md) — producing a `TrainedModel` JSON file to
  reference via `log_semiring_model_path`
- `BeamWidthConfig` internals (`to_option()` and `is_auto()` helpers) are documented inline in
  this file and in the source at `prattail/src/lib.rs`
- [architecture/pipeline-integration.md](../architecture/pipeline-integration.md) — how the pipeline
  reads options from `LanguageSpec` and applies them during codegen
