# DSL Configuration

**Updated:** 2026-02-28

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
        log_semiring_model_path: "path/to/model.json",
    }
    // ... types, terms, equations, rewrites, logic
}
```

---

## 1. Option: `beam_width`

Controls how aggressively the WFST prediction and recovery stages prune
low-probability alternatives. Beam pruning is always available -- prediction
weights are computed for all grammars.

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
none / disabled  ->  BeamWidthConfig::Disabled
1.5              ->  BeamWidthConfig::Explicit(1.5)
auto             ->  BeamWidthConfig::Auto
```

### 1.3 `to_option()` helper

`BeamWidthConfig::to_option()` converts the enum to the `Option<f64>` used
by `predict_pruned()` and `viterbi_recovery_beam()`:

| Variant             | `to_option()` result                           |
|---------------------|------------------------------------------------|
| `Disabled`          | `None` -- no pruning applied                    |
| `Explicit(w)`       | `Some(w)` -- passed directly to beam functions |
| `Auto`              | `None` -- pipeline resolves from model later    |

For `Auto`, the pipeline reads `TrainedModel::recommended_beam_width` from
the JSON file specified in `log_semiring_model_path` and replaces `Auto` with
the corresponding `Explicit(w)` before codegen. If the model file is absent
or carries no recommendation, `Auto` falls back to `Disabled`.

### 1.4 Examples

```rust
// No pruning (default -- same as omitting the option)
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
alternative. See [training-guide.md](training-guide.md) for the
full training workflow.

---

## 2. Option: `log_semiring_model_path`

A string literal naming a file path to a `TrainedModel` JSON file produced
by the training API. The path is resolved relative to the workspace root at
macro-expansion time (compile time).

### 2.1 Syntax

```rust
log_semiring_model_path: "path/to/model.json",
```

### 2.2 Usage constraints

- Required when `beam_width: auto` is specified. The DSL parser emits a
  compile error if `auto` is used without this option.
- Ignored when `beam_width` is `disabled` or an explicit float (the model
  file is not read).
- Has no effect without the `wfst-log` feature. The pipeline skips model
  loading when `wfst-log` is absent, which means `auto` degrades to
  `disabled` silently in that case.

### 2.3 Model file format

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

See [training-guide.md](training-guide.md) for how to generate this
file from a training corpus.

---

## 3. `AttributeValue` Variants

The `options { }` block parser (`macros/src/ast/language.rs`) recognises
five value forms, each mapped to an `AttributeValue` variant:

```
Float    -- any floating-point literal:    1.5, 2.0, 0.5
Int      -- any integer literal:           1, 42
Bool     -- true or false
Str      -- double-quoted string literal:  "path/to/model.json"
Keyword  -- bare identifier:              none, disabled, auto
```

Unknown option keys produce a compile-time warning (currently) and are
ignored by the pipeline.

---

## 4. Complete Example

A grammar using both options:

```rust
language! {
    name: Calculator,
    options {
        beam_width: 1.5,
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

## 5. Minimal Example (All Defaults)

When no options are needed the block can be omitted entirely.
The options default to:

```
beam_width              ->  BeamWidthConfig::Disabled
log_semiring_model_path ->  (none)
```

All grammars receive WFST-weighted dispatch automatically regardless of
whether any options are specified.

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

## 6. Option-Interaction Diagram

The two options interact when `beam_width: auto` is active. The diagram
below shows the resolution path.

```
  beam_width: auto
       |
       v
  is wfst-log enabled?
  +----+--------------------------------------------+
  | NO                                              | YES
  v                                                 v
  BeamWidthConfig::Disabled              log_semiring_model_path set?
  (auto degrades silently)               +-------------+---------------+
                                         | NO                          | YES
                                         v                             v
                                  BeamWidthConfig::Disabled     read model JSON
                                  (warning: no model path)           |
                                                                     v
                                                  recommended_beam_width present?
                                                  +------------+------------+
                                                  | NO                      | YES
                                                  v                         v
                                           Disabled                  Explicit(w)
```

---

## 7. Source Locations

| Component                    | File                                          |
|------------------------------|-----------------------------------------------|
| `AttributeValue` enum        | `macros/src/ast/language.rs`                  |
| `parse_options()` function   | `macros/src/ast/language.rs`                  |
| `BeamWidthConfig` enum       | `prattail/src/lib.rs`                         |
| `LanguageSpec` struct        | `prattail/src/lib.rs`                         |
| `predict_pruned()`           | `prattail/src/wfst.rs`                        |
| `viterbi_recovery_beam()`    | `prattail/src/recovery.rs`                    |

---

## 8. Cross-References

- [feature-gates.md](feature-gates.md) -- enabling the `wfst-log` feature,
  Cargo.toml snippets for every crate in the chain
- [training-guide.md](training-guide.md) -- producing a `TrainedModel` JSON file to
  reference via `log_semiring_model_path`
- `BeamWidthConfig` internals (`to_option()` and `is_auto()` helpers) are documented inline in
  this file and in the source at `prattail/src/lib.rs`
