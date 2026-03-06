# Recovery Tuning Guide

**Date:** 2026-03-01

Practical guide for grammar authors: configure recovery parameters,
interpret recovery diagnostics, and train recovery weights from example
corpora.

---

## Table of Contents

1. [Quick Reference](#1-quick-reference)
2. [Configuring RecoveryConfig](#2-configuring-recoveryconfig)
3. [Understanding Recovery Diagnostics](#3-understanding-recovery-diagnostics)
4. [Training Recovery Weights](#4-training-recovery-weights)
5. [Lattice Recovery](#5-lattice-recovery)
6. [Troubleshooting](#6-troubleshooting)

---

## 1. Quick Reference

### What Happens on a Syntax Error

When the parser encounters an unexpected token:

```
1. parse_Cat() returns Err(ParseError)
2. parse_Cat_recovering() catches the error
3. Cascade check: if within cascade_window of last error → suppress
4. Incremental bracket scan → (open_parens, open_braces, open_brackets)
5. wfst_recover_Cat() evaluates 7 strategies:
   a. SkipToSync (skip to nearest sync token)
   b. DeleteToken (delete one token)
   c. InsertToken (insert a missing token, bracket-aware)
   d. SubstituteToken (replace current token)
   e. SwapTokens (transpose two adjacent tokens)
   f. CategorySwitch (switch to another category via cast)
   g. viterbi_multi_step (optimal multi-step sequence)
6. Cheapest strategy wins → parser position updated
7. ParseError::RecoveryApplied pushed to error vector
```

### Recovery Messages in Parse Output

```
3:5: recovery applied: skip 2 token(s) to ';' (original: expected Int, found @)
```

The error includes:
- Source location (`3:5`)
- Recovery action description (`skip 2 token(s) to ';'`)
- Original error (`expected Int, found @`)

---

## 2. Configuring RecoveryConfig

### 2.1 Setting recovery_config in LanguageSpec

```rust
let mut spec = LanguageSpec::new("MyLang");
spec.recovery_config = RecoveryConfig {
    insert_cost: 1.5,
    bracket_insert_mult: 0.2,
    cascade_window: 4,
    ..Default::default()
};
```

The `RecoveryConfig` is consumed by the pipeline at code generation time.
All values are inlined as constants in the generated parser.

### 2.2 Per-Field Reference Table

| Field                     | Default   | Valid Range    | Effect                             |
|---------------------------|-----------|----------------|------------------------------------|
| `skip_per_token`          | 0.5       | (0, ∞)         | Cost per skipped token             |
| `delete_cost`             | 1.0       | (0, ∞)         | Cost to delete one token           |
| `substitute_cost`         | 1.5       | (0, ∞)         | Cost to substitute one token       |
| `insert_cost`             | 2.0       | (0, ∞)         | Cost to insert a phantom token     |
| `swap_cost`               | 1.25      | (0, ∞)         | Cost to swap two adjacent tokens   |
| `max_skip_lookahead`      | 32        | [1, ∞)         | Maximum skip search window         |
| `deep_nesting_threshold`  | 1000      | [0, ∞)         | Depth for skip discount            |
| `deep_nesting_skip_mult`  | 0.5       | (0, ∞)         | Skip multiplier when deep          |
| `shallow_depth_threshold` | 10        | [0, ∞)         | Depth for skip penalty             |
| `shallow_depth_skip_mult` | 2.0       | (0, ∞)         | Skip multiplier when shallow       |
| `low_bp_threshold`        | 4         | [0, 255]       | BP for skip discount               |
| `low_bp_skip_mult`        | 0.75      | (0, ∞)         | Skip multiplier at low BP          |
| `collection_insert_mult`  | 0.5       | (0, ∞)         | Insert discount in collections     |
| `group_insert_mult`       | 0.5       | (0, ∞)         | Insert discount in groups          |
| `bracket_insert_mult`     | 0.3       | (0, ∞)         | Insert discount for bracket repair |
| `mixfix_substitute_mult`  | 0.75      | (0, ∞)         | Substitute discount in mixfix      |
| `simulation_valid_mult`   | 0.5       | (0, ∞)         | Discount when simulation succeeds  |
| `simulation_fail_penalty` | 0.2       | [0, ∞)         | Penalty per sim failure token      |
| `beam_width`              | Some(3.0) | None or (0, ∞) | Viterbi beam width                 |
| `cascade_window`          | 3         | [0, ∞)         | Cascade suppression window         |

See [recovery-config.md](../../design/wfst/recovery-config.md) for
detailed semantics.

### 2.3 Example: Bracket-Heavy Grammars

Lower insert cost for closing delimiters:

```rust
RecoveryConfig {
    insert_cost: 1.5,             // base insert cost reduced from 2.0
    bracket_insert_mult: 0.2,     // strong bracket repair discount
    group_insert_mult: 0.3,       // strong group insert discount
    cascade_window: 4,            // wider cascade for bracket chains
    ..Default::default()
}
```

When a `(` is unmatched and the parser is in a Group frame:
- Insert `)` cost = 1.5 × 0.3 × 0.2 = 0.09 (very cheap)
- Skip 1 token cost = 0.5 (more expensive)

Result: the parser strongly prefers inserting the missing `)`.

### 2.4 Example: Wider Beam for Complex Errors

For grammars where errors often require multi-step repair:

```rust
RecoveryConfig {
    beam_width: Some(5.0),        // wider beam (default: 3.0)
    max_skip_lookahead: 48,       // look further ahead (default: 32)
    ..Default::default()
}
```

This lets `viterbi_multi_step()` explore more repair paths before
pruning, finding better composite repairs at the cost of slightly more
computation per error.

### 2.5 Example: Expression-Dense Languages

For grammars with high operator density (e.g. calculator, APL):

```rust
RecoveryConfig {
    cascade_window: 2,            // tighter cascade (errors are independent)
    shallow_depth_threshold: 5,   // lower shallow threshold
    low_bp_threshold: 2,          // lower BP threshold
    ..Default::default()
}
```

Operators appear frequently, so errors are typically localized to a
single operator/operand pair. A tighter cascade window reports more
errors, which is appropriate when they are genuinely independent.

---

## 3. Understanding Recovery Diagnostics

### 3.1 ParseError::RecoveryApplied Anatomy

```rust
ParseError::RecoveryApplied {
    original_error: Box<ParseError>,   // what went wrong
    repair_description: String,        // what the parser did about it
    range: Range,                      // where the error was
}
```

The `Display` implementation produces:
```
{line}:{col}: recovery applied: {repair_description} (original: {original_error})
```

### 3.2 Repair Description Strings

| Message Pattern                                     | Strategy        |
|-----------------------------------------------------|-----------------|
| `"skip N token(s) to 'X'"`                          | SkipToSync      |
| `"delete unexpected token"`                         | DeleteToken     |
| `"insert missing 'X'"`                              | InsertToken     |
| `"expected 'X' here"`                               | SubstituteToken |
| `"swap adjacent tokens"`                            | SwapTokens      |
| `"try parsing as Cat (cast Cat → Target)"`          | CategorySwitch  |
| `"delete unexpected token, skip 1 token(s) to ';'"` | Composite       |

**Notes:**
- Token names in messages (e.g. `'Semi'`, `'RParen'`) come from the
  `RECOVERY_TOKEN_NAMES_Cat` static array.
- Composite messages join component descriptions with `", "`.
- CategorySwitch messages include both the source and target categories.

### 3.3 Cast Suggestion Hints

When a token belongs to another category's FIRST set but no cast rule
exists, the parser appends a hint to the `expected` field:

```
expected Int expression
Hint: 'at' is a Proc expression, but no Proc → Float cast rule exists.
```

These hints help grammar authors identify missing cast rules.

### 3.4 Diagnosing Common Issues

**"Too many recoveries":** If the parser produces many
`RecoveryApplied` errors for a single mistake:
- The cascade window may be too small → increase `cascade_window`.
- The recovery action may not advance far enough → check if skip
  costs are too high (making skip lose to insert, which doesn't
  advance).

**"Wrong recovery chosen":** If the parser chooses a suboptimal
strategy:
- Check the cost hierarchy: is the desired strategy cheaper than
  the chosen one?
- Check Tier 3 simulation: does the desired strategy lead to a
  valid continuation? If not, it gets a penalty.
- Try adjusting the relevant base cost in `RecoveryConfig`.

---

## 4. Training Recovery Weights (wfst-log)

The `wfst-log` feature enables learning optimal strategy costs from a
corpus of erroneous inputs.

### 4.1 Preparing RecoveryTrainingExample Corpus

Create examples pairing erroneous inputs with expected repairs:

```rust
use mettail_prattail::recovery::RepairAction;
use mettail_prattail::training::RecoveryTrainingExample;

let examples = vec![
    RecoveryTrainingExample {
        input_with_error: "3 + + 5".to_string(),
        correct_input: "3 + 5".to_string(),
        error_positions: vec![2],
        expected_repairs: vec![RepairAction::DeleteToken],
    },
    RecoveryTrainingExample {
        input_with_error: "3 5 +".to_string(),
        correct_input: "3 + 5".to_string(),
        error_positions: vec![1],
        expected_repairs: vec![RepairAction::SwapTokens {
            pos_a: 1, pos_b: 2,
        }],
    },
];
```

**Guidelines for good examples:**
- Include representative errors for your grammar (missing operators,
  extra tokens, missing brackets, transpositions).
- Each example should have a clear "correct" input.
- Include at least 10-20 examples for meaningful learning.

### 4.2 Running train_recovery_weights()

```rust
use mettail_prattail::training::train_recovery_weights;

let weights = train_recovery_weights(
    &examples,
    100,    // epochs
    0.01,   // learning rate
);

println!("Trained weights: {:?}", weights);
// e.g. {"skip_per_token": 0.48, "delete_cost": 0.85, ...}
```

The SGD loop adjusts weights so that expected repairs become cheaper
than alternatives. Weights are clamped to [0.01, 10.0].

### 4.3 Applying and Validating Trained Weights

```rust
use mettail_prattail::recovery::RecoveryConfig;

let mut config = RecoveryConfig::default();
config.apply_trained_weights(&weights);

// Validate: check that the trained config produces expected repairs
// on the training corpus and on held-out examples.
```

Trained weights only affect the 5 base strategy costs. Threshold and
multiplier fields remain at their configured values.

---

## 5. Lattice Recovery (Removed)

> **Note:** The `context-sensitive-lex` feature has been removed. The always-on
> WFST architecture now resolves all lexer ambiguities at compile time, making
> runtime lattice recovery unnecessary. This section is retained for historical
> reference.

Lattice recovery was previously activated when the now-removed
`context-sensitive-lex` feature was enabled, the lexer produced a
`TokenLattice` (multiple paths), and recovery on the primary
tokenization failed or produced a high-cost repair.

### 5.2 How Alternatives Affect Recovery

For each alternative tokenization path:
1. `viterbi_multi_step()` is run on that path.
2. The repair cost is multiplied by the path's lexer weight.
3. A small penalty (0.1 × alternative index) prefers the primary
   tokenization.

The cheapest repair across all alternatives is selected.

---

## 6. Troubleshooting

### 6.1 Wrong Recovery Choice

**Symptom:** Parser recovers with "delete unexpected token" when "insert
missing ')'" would be better.

**Diagnosis:** Check the cost comparison:
- Delete: 1.0 × skip_mult × tier3_mult
- Insert `)` with unmatched `(`: 2.0 × group_insert_mult ×
  bracket_insert_mult × tier3_mult = 2.0 × 0.5 × 0.3 × tier3_mult =
  0.3 × tier3_mult

If tier3_mult is similar for both, insert (0.3) should beat delete
(1.0). If delete is winning, check:
- Are brackets actually unmatched? (BRACKET_STATE may not reflect
  the current bracket count if tokens were consumed before the error.)
- Is the frame_kind correctly identified as Group? (Check
  `frame_kind_of_Cat()`.)

**Fix:** Adjust `bracket_insert_mult` or `group_insert_mult` lower.

### 6.2 Too Many Suppressed Errors

**Symptom:** Only 1-2 errors reported for an input with many independent
mistakes.

**Diagnosis:** The cascade window is too wide, suppressing genuine errors.

**Fix:** Decrease `cascade_window`:

```rust
RecoveryConfig {
    cascade_window: 1,   // only suppress immediately adjacent errors
    ..Default::default()
}
```

### 6.3 Cross-Category Recovery Missing

**Symptom:** Error "expected Int" when the token is a valid Bool, and
`BoolToInt` cast exists, but no CategorySwitch repair is offered.

**Diagnosis:** Check:
1. Does `CROSS_CAT_CASTS_Int` contain a `"Bool"` entry?
2. Is the error token's ID in the Bool FIRST set?
3. Is the grammar multi-category? (Single-category grammars skip
   CategorySwitch entirely.)

**Fix:** Verify that the cast rule is correctly defined in the grammar
and that the FIRST set for the source category includes the token.

### 6.4 ParseSimulator Inactive

**Symptom:** Tier 3 simulation always returns `ValidContinuation` or
always returns `FailedAt(0)`.

**Diagnosis:** Check:
1. Are `SIM_FIRST_SETS` non-empty? (If FIRST sets are empty, every
   token fails the first check.)
2. Are `SIM_FOLLOW_SETS` non-empty? (If FOLLOW sets are empty, the
   simulator never recognizes category boundaries.)
3. Are `SIM_INFIX_SETS` non-empty? (If infix sets are empty, the
   simulator never recognizes infix continuation.)

**Fix:** Ensure the grammar has properly defined rules with operators.
The prediction engine computes FIRST/FOLLOW sets from the grammar rules.
Empty sets indicate rules without terminals (unusual).

---

**Cross-references:**

- [RecoveryConfig](../../design/wfst/recovery-config.md) — full
  parameter specification and worked tuning examples
- [Extended Recovery Strategies](../../design/wfst/extended-recovery-strategies.md) —
  7-strategy evaluation and cost hierarchy
- [Recovery State Propagation](../../architecture/wfst/recovery-state-propagation.md) —
  thread-local state and generated code anatomy
- [Error Recovery (base)](../../design/wfst/error-recovery.md) —
  3-tier cost model
- [Cascade Suppression](../../theory/wfst/cascade-suppression.md) —
  formal cascade prevention model
