# Recovery State Propagation

**Date:** 2026-03-01

Architecture of the thread-local state infrastructure, pipeline emission
stages, and generated code anatomy for PraTTaIL's WFST error recovery
system. The core design principle is **zero overhead on the happy path**:
no recovery-related code executes during successful parsing.

---

## Table of Contents

1. [Overview](#1-overview)
2. [Thread-Local State Cells](#2-thread-local-state-cells)
3. [LazyLock ParseSimulator (Tier 3)](#3-lazylock-parsesimulator-tier-3)
4. [Pipeline Emission Dependency Graph](#4-pipeline-emission-dependency-graph)
5. [Generated wfst_recover_Cat Anatomy](#5-generated-wfst_recover_cat-anatomy)
6. [Generated parse_Cat_recovering Anatomy](#6-generated-parse_cat_recovering-anatomy)
7. [ParseError::RecoveryApplied](#7-parseerrorrecoveryapplied)
8. [Token Names and describe()](#8-token-names-and-describe)
9. [Lattice-Aware Recovery](#9-lattice-aware-recovery)
10. [Zero-Overhead Summary](#10-zero-overhead-summary)
11. [Source Reference](#11-source-reference)

---

## 1. Overview

The recovery system uses four categories of state:

| Category                     | Storage                          | Scope         | Initialized  |
|------------------------------|----------------------------------|---------------|-------------|
| Bracket balance              | `Cell<(usize, u16, u16, u16)>`   | Per-category  | On min_bp=0 |
| Last error position          | `Cell<usize>`                    | Per-category  | On min_bp=0 |
| Frame depth + kind           | `Cell<(u16, u8)>`                | Per-category  | On each drive loop |
| ParseSimulator               | `LazyLock<ParseSimulator>`       | Global        | On first error |

All four are thread-local (`thread_local!` macro) or `static`
(`LazyLock`). None are accessed on the happy path.

---

## 2. Thread-Local State Cells

### 2.1 BRACKET_STATE_Cat

```rust
thread_local! {
    static BRACKET_STATE_Cat: Cell<(usize, u16, u16, u16)> =
        Cell::new((0, 0, 0, 0));
}
```

**Fields:** `(last_scanned_pos, open_parens, open_braces, open_brackets)`

**Purpose:** Provides Tier 2 bracket balance context to the recovery
function. Tracks the number of unmatched opening delimiters scanned so
far.

**Incremental scanning:** On each error, the bracket scanner resumes
from `last_scanned_pos` rather than re-scanning from position 0:

```rust
let (last, mut op, mut ob, mut ok) = BRACKET_STATE_Cat.with(|c| c.get());
let scan_to = min(*pos, tokens.len());
for i in last..scan_to {
    match &tokens[i].0 {
        Token::LParen   => op = op.saturating_add(1),
        Token::RParen   => op = op.saturating_sub(1),
        Token::LBrace   => ob = ob.saturating_add(1),
        Token::RBrace   => ob = ob.saturating_sub(1),
        Token::LBracket => ok = ok.saturating_add(1),
        Token::RBracket => ok = ok.saturating_sub(1),
        _ => {}
    }
}
BRACKET_STATE_Cat.with(|c| c.set((scan_to, op, ob, ok)));
```

**Complexity comparison:**

```
  Old (O(pos) scan):            New (incremental scan):

  Error 1 at pos 100:           Error 1 at pos 100:
    scan 0..100 (100 tokens)      scan 0..100 (100 tokens)

  Error 2 at pos 200:           Error 2 at pos 200:
    scan 0..200 (200 tokens)      scan 100..200 (100 tokens)

  Error 3 at pos 300:           Error 3 at pos 300:
    scan 0..300 (300 tokens)      scan 200..300 (100 tokens)

  Total: 100+200+300 = 600      Total: 100+100+100 = 300
         O(pos × num_errors)           O(total_tokens) amortized
```

**Reset:** On `min_bp == 0` (top-level parse), the bracket state resets
to `(0, 0, 0, 0)`, ensuring clean state for each parse invocation.

### 2.2 LAST_ERROR_POS_Cat

```rust
thread_local! {
    static LAST_ERROR_POS_Cat: Cell<usize> = Cell::new(usize::MAX);
}
```

**Purpose:** Cascade prevention. Stores the position of the most recent
genuine error. Errors within `cascade_window` tokens of this position
are suppressed.

**Sentinel:** `usize::MAX` means "no previous error." The overflow
check `*pos <= last_err + cascade_window` wraps around safely: when
`last_err = usize::MAX`, `last_err + k` wraps to a small value, and
`*pos <= small_value` is false for any valid position, so no false
suppression occurs.

**Reset:** On `min_bp == 0`, resets to `usize::MAX`.

See [cascade-suppression.md](../../theory/wfst/cascade-suppression.md)
for the formal model.

### 2.3 FRAME_STATE_Cat

```rust
thread_local! {
    static FRAME_STATE_CAT: Cell<(u16, u8)> = Cell::new((0, 9));
}
```

**Fields:** `(depth, frame_kind)`

**Purpose:** Provides Tier 1 frame context to the recovery function.
Updated at the top of each trampoline `'drive` loop iteration:

```rust
FRAME_STATE_CAT.with(|c| c.set(
    (stack.len() as u16, frame_kind_of_Cat(&stack))
));
```

**Frame kind encoding:**

| Value | FrameKind   | Classified from variant name prefix      |
|-------|-------------|------------------------------------------|
| 0     | Prefix      | `UnaryPrefix_*`                          |
| 1     | InfixRHS    | `InfixRHS`                               |
| 2     | Postfix     | (reserved)                               |
| 3     | Collection  | `CollectionElem_*`                       |
| 4     | Group       | `GroupClose`                             |
| 5     | Mixfix      | `Mixfix_*`                               |
| 6     | Lambda      | `LambdaBody_*`                           |
| 7     | Dollar      | `Dollar*` or `Ddollar*`                  |
| 8     | CastWrap    | `CastWrap_*`                             |
| 9     | Other       | (default, catch-all)                     |

The `frame_kind_of_Cat()` helper function maps the top-of-stack frame
variant to its kind code.

**Overhead:** Writing a `Cell<(u16, u8)>` is a single pointer-sized
store (3 bytes packed). The cost is negligible compared to the
per-iteration work in the trampoline loop.

### 2.4 FRAME_POOL_Cat

```rust
thread_local! {
    static FRAME_POOL_Cat: Cell<Vec<Frame_Cat>> = Cell::new(Vec::new());
}
```

This is the existing frame pool for the trampolined parser (see
[trampoline architecture](../../architecture/generated-code-anatomy.md)).
It is not recovery-specific but is mentioned here for completeness as the
fourth thread-local Cell used by the parser.

---

## 3. LazyLock\<ParseSimulator\> (Tier 3)

### 3.1 Static Arrays

Three static arrays provide the data for the ParseSimulator:

```rust
static SIM_FIRST_SETS: &[(&str, &[u16])] = &[
    ("Int", &[3_u16, 4_u16]),     // Integer, Ident
    ("Bool", &[5_u16, 6_u16]),    // True, False
];

static SIM_FOLLOW_SETS: &[(&str, &[u16])] = &[
    ("Int", &[0_u16, 1_u16, 7_u16]),  // Plus, Star, Semi
    ("Bool", &[2_u16, 7_u16]),         // And, Semi
];

static SIM_INFIX_SETS: &[(&str, &[u16])] = &[
    ("Int", &[0_u16, 1_u16]),    // Plus, Star
    ("Bool", &[2_u16]),          // And
];
```

Token IDs are assigned by the `TokenIdMap` during pipeline extraction.

### 3.2 LazyLock Initialization

```rust
static PARSE_SIMULATOR: LazyLock<ParseSimulator> =
    LazyLock::new(|| {
        ParseSimulator::from_flat(
            SIM_FIRST_SETS,
            SIM_FOLLOW_SETS,
            SIM_INFIX_SETS,
            5,  // lookahead depth
        )
    });
```

The `ParseSimulator` is constructed lazily — only on the first error in
any category. Subsequent errors reuse the same instance. This avoids any
allocation cost on the happy path.

### 3.3 token_to_id() Helper

```rust
fn token_to_id(t: &Token) -> u16 {
    match t {
        Token::Plus      => 0,
        Token::Star      => 1,
        Token::And       => 2,
        Token::Integer(_)=> 3,
        Token::Ident(_)  => 4,
        // ... (all Token variants in grammar)
        _ => u16::MAX,   // unknown token → ID that matches nothing
    }
}
```

Called only on error paths to convert token slices to ID arrays for
simulation.

---

## 4. Pipeline Emission Dependency Graph

```
extract_data()
    │
    ├── compute_first_follow()
    │       │
    │       ├── FirstSets ──────────────┐
    │       └── FollowSets ─────────────┤
    │                                   │
    ├── build_recovery_wfsts()          │
    │       │                           │
    │       └── RecoveryWfst[] ─────────┤
    │                                   │
    ├── compute_binding_powers()        │
    │       │                           │
    │       └── BPTable ────────────────┤
    │                                   │
    └── compute_cast_analysis()         │
            │                           │
            └── CrossCatCasts ──────────┤
                                        │
generate_code()                         │
    │                                   │
    ├── emit_recovery_wfst_static() ◄───┤
    │       │                           │
    │       ├── RECOVERY_SYNC_TOKENS_Cat│
    │       └── RECOVERY_TOKEN_NAMES_Cat│
    │                                   │
    ├── emit_parse_simulator_static() ◄─┘
    │       │
    │       ├── SIM_FIRST_SETS
    │       ├── SIM_FOLLOW_SETS
    │       ├── SIM_INFIX_SETS
    │       └── PARSE_SIMULATOR (LazyLock)
    │
    ├── emit_token_to_id_fn()
    │       └── token_to_id()
    │
    ├── emit CROSS_CAT_CASTS_Cat
    │       └── CROSS_CAT_CASTS_Cat (&[(&str, &[u16])])
    │
    ├── generate_wfst_recovery_fn()
    │       └── wfst_recover_Cat()
    │
    └── write_trampolined_parser_recovering_wfst()
            ├── BRACKET_STATE_Cat
            ├── LAST_ERROR_POS_Cat
            └── parse_Cat_recovering()
```

---

## 5. Generated wfst_recover_Cat Anatomy

The `generate_wfst_recovery_fn()` pipeline stage emits one
`wfst_recover_Cat()` function per category.

### 5.1 Parameters

```rust
fn wfst_recover_Cat<'a>(
    tokens: &[(Token<'a>, Range)],
    pos: &mut usize,
    depth: usize,
    min_bp: u8,
    open_parens: u16,
    open_braces: u16,
    open_brackets: u16,
) -> Option<String>
```

### 5.2 Token-to-ID Conversion

Only on the error path:

```rust
let sim_ids: Vec<u16> = tokens[new_pos..]
    .iter()
    .map(|(t, _)| token_to_id(t))
    .collect();
```

### 5.3 7-Strategy Evaluation Structure

```
1. Read FRAME_STATE_Cat → (frame_depth, frame_kind)
2. Compute Tier 1 multipliers (skip, BP, frame)
3. Strategy 1: SkipToSync (sync_tokens match arm)
4. Strategy 2: DeleteToken (cost 1.0 × combined_skip_mult)
5. Strategy 3: InsertToken (bracket-aware: RParen/RBrace/RBracket)
6. Strategy 4: SubstituteToken (cost 1.5 × sub_mult)
7. Tier 3: ParseSimulator rescoring
8. Strategy 7: viterbi_multi_step (full repair lattice)
9. Strategy 6: CategorySwitch (CROSS_CAT_CASTS check)
10. Winner: apply best_pos, return Some(best_desc) or None
```

### 5.4 Tier 1/2/3 Multiplier Application

**Tier 1 (frame context):**
```rust
let skip_mult = if effective_depth > 1000 { 0.5 }
    else if effective_depth < 10 { 2.0 } else { 1.0 };
let bp_mult = if binding_power < 4 { 0.75 } else { 1.0 };
let frame_skip_mult = if frame_kind == 1 { 0.75 } else { 1.0 };
let combined_skip_mult = skip_mult * bp_mult * frame_skip_mult;
```

**Tier 2 (bracket balance):**
```rust
if open_parens > 0 {
    let cost = base_insert * 0.3;  // strongly prefer closing parens
}
```

**Tier 3 (simulation):**
```rust
let sim_result = PARSE_SIMULATOR.simulate_after_repair(&sim_ids, 0, "Cat");
let sim_mult = PARSE_SIMULATOR.cost_multiplier(&sim_result);
best_cost *= sim_mult;
```

### 5.5 Return Value

`Option<String>` — the human-readable repair description, or `None` if
no recovery is possible. The string is passed to
`ParseError::RecoveryApplied`.

---

## 6. Generated parse_Cat_recovering Anatomy

The `write_trampolined_parser_recovering_wfst()` pipeline stage emits
one `parse_Cat_recovering()` function per category.

### 6.1 Thread-Local Resets on min_bp == 0

```rust
if min_bp == 0 {
    BRACKET_STATE_Cat.with(|c| c.set((0, 0, 0, 0)));
    LAST_ERROR_POS_Cat.with(|c| c.set(usize::MAX));
}
```

This ensures clean state at the start of each top-level parse.

### 6.2 Delegate to parse_Cat

```rust
match parse_Cat_own(tokens, pos, min_bp) {
    Ok(v) => Some(v),
    Err(e) => { /* recovery path */ }
}
```

The recovering function calls the non-recovering parser and only
activates recovery on `Err`.

### 6.3 Recovery Path

```rust
Err(e) => {
    // Cascade check
    let last_err = LAST_ERROR_POS_Cat.with(|c| c.get());
    if last_err != usize::MAX && *pos <= last_err + CASCADE_WINDOW {
        if *pos < tokens.len() { *pos += 1; }
        return None;
    }
    LAST_ERROR_POS_Cat.with(|c| c.set(*pos));

    // Incremental bracket scan
    let (op, ob, ok) = BRACKET_STATE_Cat.with(|c| { /* scan */ });

    // Recovery
    let repair_range = e.range();
    match wfst_recover_Cat(tokens, pos, 0, min_bp, op, ob, ok) {
        Some(desc) => errors.push(ParseError::RecoveryApplied {
            original_error: Box::new(e),
            repair_description: desc,
            range: repair_range,
        }),
        None => errors.push(e),
    }
    None
}
```

### 6.4 Emit ParseError::RecoveryApplied

When recovery succeeds, the original error is wrapped in
`RecoveryApplied` with the repair description. When recovery fails, the
original error is pushed unchanged.

---

## 7. ParseError::RecoveryApplied

### 7.1 Structure

```rust
ParseError::RecoveryApplied {
    original_error: Box<ParseError>,   // the original parse error
    repair_description: String,        // e.g. "skip 2 token(s) to ';'"
    range: Range,                      // source location of the error
}
```

### 7.2 Display Format

```
{line}:{col}: recovery applied: {repair_description} (original: {original_error})
```

Example:
```
3:5: recovery applied: skip 2 token(s) to ';' (original: expected Int, found @)
```

The `expected` field in `UnexpectedToken` uses `Cow<'static, str>` to
avoid allocation for static category names. Cast suggestion hints append
to this field dynamically.

---

## 8. Token Names and describe()

### 8.1 RECOVERY_TOKEN_NAMES_Cat

Each category emits a token name table indexed by TokenId:

```rust
static RECOVERY_TOKEN_NAMES_Int: &[&str] = &[
    "Plus", "Star", "Integer", "Ident", "RParen", "Semi", "Eof",
];
```

### 8.2 Human-Readable Descriptions

`RepairAction::describe(token_names)` produces user-facing messages:

| Action                              | Description                               |
|-------------------------------------|-------------------------------------------|
| `SkipToSync { skip_count: 2, .. }`  | `"skip 2 token(s) to 'Semi'"`            |
| `DeleteToken`                       | `"delete unexpected token"`               |
| `InsertToken { token: RParen }`     | `"insert missing ')'"`                   |
| `SubstituteToken { .. }`            | `"expected 'Plus' here"`                  |
| `SwapTokens { .. }`                 | `"swap adjacent tokens"`                  |
| `CategorySwitch { to: "Bool", .. }` | `"try parsing as Bool (cast Bool → Int)"` |
| `Composite { steps: [del, skip] }`  | `"delete unexpected token, skip 1 token(s) to ';'"` |

---

## 9. Lattice-Aware Recovery (context-sensitive-lex)

When the `context-sensitive-lex` feature is enabled, the lexer produces
a `TokenLattice` with multiple tokenization paths. The recovery system
can exploit alternative tokenizations.

### 9.1 alternative_paths()

`TokenLattice::alternative_paths(start, k)` extracts up to *k* paths
from the lattice starting at position `start`. Each path is a
`(Vec<TokenId>, TropicalWeight)` pair.

### 9.2 lattice_recovery()

```rust
pub fn lattice_recovery(
    alternative_token_ids: &[(Vec<TokenId>, TropicalWeight)],
    pos: usize,
    sync_tokens: &BTreeSet<TokenId>,
    config: &RecoveryConfig,
) -> Option<RepairResult>
```

For each alternative tokenization:
1. Run `viterbi_multi_step()` on that tokenization.
2. Multiply the repair cost by the alternative's lexer weight.
3. Add a penalty of `0.1 × alternative_index` (prefer primary
   tokenization).
4. Keep the cheapest result across all alternatives.

### 9.3 Cost Formula

```
cost(alt_i) = viterbi_cost(alt_i) × lexer_weight(alt_i)
            + 0.1 × i
```

The primary tokenization (`i = 0`) has zero penalty. Alternatives with
lower lexer weight (= higher tropical cost = less likely tokenization)
are penalized both by their lexer weight and by the index penalty.

---

## 10. Zero-Overhead Summary

| Component                    | Happy Path    | Error Path               |
|------------------------------|---------------|--------------------------|
| parse_Cat()                  | Called        | Not called               |
| parse_Cat_recovering()       | Delegates     | Full recovery logic      |
| BRACKET_STATE_Cat            | Not touched   | Incremental scan         |
| LAST_ERROR_POS_Cat           | Not touched   | Cascade check + update   |
| FRAME_STATE_Cat              | Written (3 bytes) | Read by wfst_recover |
| PARSE_SIMULATOR              | Not initialized | Lazy init on first use |
| token_to_id()                | Not called    | Called for sim + Viterbi  |
| wfst_recover_Cat()           | Not called    | Full 7-strategy eval     |
| RecoveryConfig constants     | Not read      | Read by multipliers      |
| CROSS_CAT_CASTS_Cat          | Not read      | Iterated on error        |

**FRAME_STATE_Cat** is the only recovery-related cell written on the
happy path (at the top of each trampoline `'drive` loop). The write is a
3-byte `Cell::set()` — cheaper than a branch prediction miss. All other
recovery infrastructure is completely idle during successful parsing.

---

## 11. Source Reference

| Symbol                                  | Location                              |
|-----------------------------------------|---------------------------------------|
| `BRACKET_STATE_Cat`                     | `prattail/src/pipeline.rs:2099`       |
| `LAST_ERROR_POS_Cat`                    | `prattail/src/pipeline.rs:2101`       |
| `FRAME_STATE_Cat`                       | `prattail/src/trampoline.rs:1030`     |
| `frame_kind_of_Cat()`                   | `prattail/src/trampoline.rs:1041`     |
| `FRAME_POOL_Cat`                        | `prattail/src/trampoline.rs` (pool)   |
| `emit_recovery_wfst_static()`           | `prattail/src/pipeline.rs:1622`       |
| `emit_parse_simulator_static()`         | `prattail/src/pipeline.rs:1695`       |
| `emit_token_to_id_fn()`                 | `prattail/src/pipeline.rs:1774`       |
| `generate_wfst_recovery_fn()`           | `prattail/src/pipeline.rs:1831`       |
| `write_trampolined_parser_recovering_wfst()` | `prattail/src/pipeline.rs:2070` |
| `RECOVERY_TOKEN_NAMES_Cat`              | `prattail/src/pipeline.rs:1666`       |
| `ParseError::RecoveryApplied`           | `prattail/src/runtime_types.rs:93–97` |
| `RepairAction::describe()`              | `prattail/src/recovery.rs:332–361`    |
| `lattice_recovery()`                    | `prattail/src/recovery.rs:1709–1750`  |
| `CROSS_CAT_CASTS_Cat`                   | `prattail/src/pipeline.rs:1180`       |
| `cast_suggestions`                      | `prattail/src/trampoline.rs:677`      |

**Cross-references:**

- [pipeline-integration.md](pipeline-integration.md) — general pipeline
  data flow
- [error-recovery.md](../../design/wfst/error-recovery.md) — base
  recovery architecture
- [extended-recovery-strategies.md](../../design/wfst/extended-recovery-strategies.md) —
  7-strategy evaluation
- [recovery-config.md](../../design/wfst/recovery-config.md) — all
  config parameters
- [cascade-suppression.md](../../theory/wfst/cascade-suppression.md) —
  absorbing-state model
