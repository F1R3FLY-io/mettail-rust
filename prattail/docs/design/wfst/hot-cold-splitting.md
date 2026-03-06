# A2: Weight-Driven Hot/Cold Path Splitting

**Date:** 2026-03-01

---

## Table of Contents

1. [Problem](#1-problem)
2. [Mechanism](#2-mechanism)
3. [Weight Scale](#3-weight-scale)
4. [Generated Code](#4-generated-code)
5. [L1 I-Cache Analysis](#5-l1-i-cache-analysis)
6. [Interaction with NFA Merged Arms](#6-interaction-with-nfa-merged-arms)
7. [Correctness](#7-correctness)
8. [Source References](#8-source-references)

---

## 1. Problem

The category dispatch function `parse_<Cat>()` is the entry point for parsing
each grammar category.  When a category has cross-category infix rules and cast
rules, the dispatch function contains a `match` expression over the lookahead
token, with one arm per dispatch alternative.  After WFST weight assignment and
sorting, these arms are ordered by likelihood -- but they are all emitted inline
in a single function body.

This creates two problems:

**Instruction cache bloat.**  Every arm contributes to the instruction
footprint of `parse_<Cat>()`.  On a typical x86-64 processor with a 32 KiB L1
instruction cache (64-byte cache lines), a function with 8--12 dispatch arms
can span 20+ cache lines.  When parsing a stream of tokens, the hot path
(direct dispatches, casts) executes repeatedly while cold arms (lookahead,
variable fallback) execute rarely or never.  The cold arms nonetheless occupy
instruction cache lines, evicting useful hot code.

**Branch prediction pollution.**  Modern CPUs use branch target buffers (BTBs)
that associate branch instruction addresses with predicted targets.  When cold
arms share BTB entries with hot arms due to spatial proximity, the predictor
sees mixed history, degrading prediction accuracy for the common case.

### Quantifying the impact

Consider a category `Bool` with the following dispatch arms in the generated
parser:

| Arm | Token                               | Weight | Frequency |
|-----|-------------------------------------|--------|-----------|
| 1   | `Integer` (deterministic cross-cat) | 0.0    | ~40%      |
| 2   | `KwTrue` / `KwFalse` (direct)       | 0.0    | ~30%      |
| 3   | `Ident` (backtracking cross-cat)    | 0.5    | ~15%      |
| 4   | `Ident` (lookahead)                 | 1.0    | ~5%       |
| 5   | `Ident` (variable)                  | 2.0    | ~10%      |

Arms 1--3 account for ~85% of dispatches.  Arms 4--5 contribute ~200 bytes of
machine code that pollute the i-cache on every invocation of `parse_Bool()`,
even though they execute only ~15% of the time.

---

## 2. Mechanism

The hot/cold splitting optimization is implemented in `write_category_dispatch()`
(`dispatch.rs`).  After the dispatch arms are collected and sorted by WFST
weight (lowest first), the function partitions them into two sets:

### 2.1 Algorithm

```
function emit_dispatch(category, sorted_arms):
    COLD_THRESHOLD := 1.0

    cold_start := first index i where sorted_arms[i].weight >= COLD_THRESHOLD

    if cold_start is None:
        ── All arms are hot: emit single function (no split)
        emit parse_<Cat>() with all arms + wildcard -> parse_<Cat>_own()

    else if cold_start == 0:
        ── All arms are cold: emit single function (no split)
        emit parse_<Cat>() with all arms + wildcard -> parse_<Cat>_own()

    else:
        ── Mixed: split into hot and cold
        hot_arms  := sorted_arms[0 .. cold_start)
        cold_arms := sorted_arms[cold_start ..)

        emit parse_<Cat>_cold() with:
            #[cold] #[inline(never)]
            cold_arms + wildcard -> parse_<Cat>_own()

        emit parse_<Cat>() with:
            hot_arms + wildcard -> parse_<Cat>_cold()
```

### 2.2 Partitioning rules

| Condition                    | Result                                  |
|------------------------------|-----------------------------------------|
| All arms have weight < 1.0   | No split; single function with all arms |
| All arms have weight >= 1.0  | No split; single function with all arms |
| Some arms < 1.0, some >= 1.0 | Split at the boundary                   |

The split is only applied when there are **both** hot and cold arms.  Splitting
when all arms fall on one side of the threshold would add an unnecessary
function call without any cache benefit.

### 2.3 Threshold selection

The threshold `COLD_THRESHOLD = 1.0` is chosen to align with the weight scale
(see Section 3).  Specifically:

- `weight < 1.0` covers Direct (0.0), Grouping (0.0), deterministic
  CrossCategory (0.0), backtracking CrossCategory (0.5), and Cast (0.5) --
  all the dispatch actions that are either deterministic or require only a
  single save/restore.

- `weight >= 1.0` covers Lookahead (1.0+) and Variable (2.0) -- actions
  that require multi-token lookahead or serve as last-resort fallbacks.

This boundary reflects a natural break in execution cost: hot arms are O(1)
dispatch, cold arms involve speculative multi-token parsing or are the
catch-all variable handler.

---

## 3. Weight Scale

The following table summarizes the weight assignment from
`compute_action_weight()` in `wfst.rs`, annotated with hot/cold classification
under `COLD_THRESHOLD = 1.0`:

| Action Kind                       | Weight      | Path | Rationale                          |
|-----------------------------------|-------------|------|------------------------------------|
| `Direct`                          | 0.0         | Hot  | Unambiguous token-to-rule mapping  |
| `Grouping`                        | 0.0         | Hot  | Structural delimiter, always valid |
| `CrossCategory` (no backtrack)    | 0.0         | Hot  | Unique token in source category    |
| `CrossCategory` (needs backtrack) | 0.5         | Hot  | Shared token, try source first     |
| `Cast`                            | 0.5         | Hot  | Type coercion, slightly penalized  |
| `Lookahead`                       | 1.0 + order | Cold | Requires reading extra tokens      |
| `Variable`                        | 2.0         | Cold | Last-resort identifier fallback    |

The weight assignment function:

```rust
fn compute_action_weight(
    _token_name: &str,
    action: &DispatchAction,
    _category: &str,
    _first_sets: &HashMap<String, FirstSet>,
    _overlaps: &HashMap<(String, String), CrossCategoryOverlap>,
    order: usize,
) -> TropicalWeight {
    match action {
        DispatchAction::Direct { .. }    => TropicalWeight::new(0.0),
        DispatchAction::Grouping { .. }  => TropicalWeight::new(0.0),
        DispatchAction::CrossCategory { needs_backtrack, .. } => {
            if *needs_backtrack {
                TropicalWeight::new(0.5)
            } else {
                TropicalWeight::new(0.0)
            }
        },
        DispatchAction::Cast { .. }      => TropicalWeight::new(0.5),
        DispatchAction::Lookahead { .. } => TropicalWeight::new(1.0 + order as f64),
        DispatchAction::Variable { .. }  => TropicalWeight::new(2.0),
    }
}
```

### Weight distribution in the RhoCalc grammar

The RhoCalc grammar has 4 categories: `Proc`, `Name`, `Int`, `Bool`.  The
dispatch weight distribution for category `Bool` (which has cross-category
comparison rules from `Int`):

```
┌────────────────────────────────────────────────────────────────────┐
│ Hot zone (weight < 1.0)                                            │
│ ├── Integer  → deterministic cross-cat (Eq, Lt, Gt, ...)   w = 0.0 │
│ ├── KwTrue   → direct (BoolLit)                            w = 0.0 │
│ ├── KwFalse  → direct (BoolLit)                            w = 0.0 │
│ ├── Float    → deterministic cross-cat                     w = 0.0 │
│ └── Ident    → backtracking cross-cat                      w = 0.5 │
├──────────────────── COLD_THRESHOLD = 1.0 ──────────────────────────┤
│ Cold zone (weight >= 1.0)                                          │
│ ├── Ident    → lookahead                                   w = 1.0 │
│ └── Ident    → variable fallback                           w = 2.0 │
└────────────────────────────────────────────────────────────────────┘
```

---

## 4. Generated Code

### 4.1 Before: Single function with all arms

Without hot/cold splitting, all dispatch arms are inlined in a single
`parse_Bool()` function:

```rust
fn parse_Bool<'a>(
    tokens: &[(Token<'a>, Range)],
    pos: &mut usize,
    min_bp: u8,
) -> Result<Bool, ParseError> {
    if *pos >= tokens.len() {
        let eof_range = tokens.last().map(|(_, r)| *r).unwrap_or(Range::zero());
        return Err(ParseError::UnexpectedEof {
            expected: Cow::Borrowed("Bool"),
            range: eof_range,
        });
    }
    match &tokens[*pos].0 {
        // ── Hot arms (weight < 1.0) ──
        Token::Integer(_) => {                           // w = 0.0
            let left = parse_Int(tokens, pos, 0)?;
            expect_token(tokens, pos, |t| matches!(t, Token::EqEq), "==")?;
            let right = parse_Int(tokens, pos, 0)?;
            Ok(Bool::Eq(Box::new(left), Box::new(right)))
        },
        Token::KwTrue => {                               // w = 0.0
            *pos += 1;
            Ok(Bool::BoolLit(true))
        },
        Token::KwFalse => {                              // w = 0.0
            *pos += 1;
            Ok(Bool::BoolLit(false))
        },
        Token::Ident(_) => {                             // w = 0.5
            let saved = *pos;
            if let Ok(left) = parse_Int(tokens, pos, 0) {
                if peek_token(tokens, *pos)
                    .map_or(false, |t| matches!(t, Token::EqEq))
                {
                    *pos += 1;
                    let right = parse_Int(tokens, pos, 0)?;
                    return Ok(Bool::Eq(Box::new(left), Box::new(right)));
                }
            }
            *pos = saved;
            parse_Bool_own(tokens, pos, min_bp)
        },
        // ── Cold arms (weight >= 1.0) ──
        Token::LParen => {                               // w = 1.0
            // lookahead disambiguation ...
            let saved = *pos;
            *pos += 1;
            match &tokens[*pos].0 {
                Token::Integer(_) => { /* ... */ },
                _ => { *pos = saved; parse_Bool_own(tokens, pos, min_bp) }
            }
        },
        _ => parse_Bool_own(tokens, pos, min_bp),        // w = +inf
    }
}
```

All arms, regardless of execution frequency, occupy the same instruction cache
footprint.

### 4.2 After: Hot function + cold helper

With hot/cold splitting, the cold arms are extracted into a separate function
annotated with `#[cold]` and `#[inline(never)]`:

```rust
#[cold]
#[inline(never)]
fn parse_Bool_cold<'a>(
    tokens: &[(Token<'a>, Range)],
    pos: &mut usize,
    min_bp: u8,
) -> Result<Bool, ParseError> {
    match &tokens[*pos].0 {
        Token::LParen => {                               // w = 1.0
            // lookahead disambiguation ...
            let saved = *pos;
            *pos += 1;
            match &tokens[*pos].0 {
                Token::Integer(_) => { /* ... */ },
                _ => { *pos = saved; parse_Bool_own(tokens, pos, min_bp) }
            }
        },
        _ => parse_Bool_own(tokens, pos, min_bp),        // fallback
    }
}

fn parse_Bool<'a>(
    tokens: &[(Token<'a>, Range)],
    pos: &mut usize,
    min_bp: u8,
) -> Result<Bool, ParseError> {
    if *pos >= tokens.len() {
        let eof_range = tokens.last().map(|(_, r)| *r).unwrap_or(Range::zero());
        return Err(ParseError::UnexpectedEof {
            expected: Cow::Borrowed("Bool"),
            range: eof_range,
        });
    }
    match &tokens[*pos].0 {
        // ── Hot arms only ──
        Token::Integer(_) => {                           // w = 0.0
            let left = parse_Int(tokens, pos, 0)?;
            expect_token(tokens, pos, |t| matches!(t, Token::EqEq), "==")?;
            let right = parse_Int(tokens, pos, 0)?;
            Ok(Bool::Eq(Box::new(left), Box::new(right)))
        },
        Token::KwTrue => {                               // w = 0.0
            *pos += 1;
            Ok(Bool::BoolLit(true))
        },
        Token::KwFalse => {                              // w = 0.0
            *pos += 1;
            Ok(Bool::BoolLit(false))
        },
        Token::Ident(_) => {                             // w = 0.5
            let saved = *pos;
            if let Ok(left) = parse_Int(tokens, pos, 0) {
                if peek_token(tokens, *pos)
                    .map_or(false, |t| matches!(t, Token::EqEq))
                {
                    *pos += 1;
                    let right = parse_Int(tokens, pos, 0)?;
                    return Ok(Bool::Eq(Box::new(left), Box::new(right)));
                }
            }
            *pos = saved;
            parse_Bool_own(tokens, pos, min_bp)
        },
        _ => parse_Bool_cold(tokens, pos, min_bp),      // route to cold helper
    }
}
```

### 4.3 Key differences

| Aspect                 | Before (single function) | After (hot/cold split)       |
|------------------------|--------------------------|------------------------------|
| `parse_Bool()` size    | All arms inline          | Hot arms only                |
| Cold arm location      | Same function body       | Separate `parse_Bool_cold()` |
| Wildcard fallback      | `parse_Bool_own()`       | `parse_Bool_cold()`          |
| Cold function wildcard | N/A                      | `parse_Bool_own()`           |
| `#[cold]` annotation   | None                     | On cold helper               |
| `#[inline(never)]`     | None                     | On cold helper               |

---

## 5. L1 I-Cache Analysis

### 5.1 Cache line arithmetic

On x86-64 (Intel/AMD), the L1 instruction cache is typically 32 KiB with
64-byte cache lines (512 cache lines total).  A Rust `match` arm on a
token enum compiles to approximately:

| Arm type                         | Machine code size | Cache lines |
|----------------------------------|-------------------|-------------|
| Direct dispatch (simple)         | 40--80 bytes      | 1--2        |
| Cross-category with save/restore | 100--160 bytes    | 2--3        |
| Lookahead disambiguation         | 150--250 bytes    | 3--4        |
| Variable fallback                | 60--100 bytes     | 1--2        |

A category with 8 dispatch arms (4 hot, 2 lookahead, 2 variable) might
produce:

| Configuration     | Estimated size | Cache lines |
|-------------------|----------------|-------------|
| All inline        | ~900 bytes     | ~14         |
| Hot function only | ~500 bytes     | ~8          |
| Cold helper       | ~400 bytes     | ~7          |

The hot function shrinks by ~44%, fitting in fewer cache lines.  Since the
hot function is called on every token dispatch and the cold helper is called
only when an unrecognized token is seen, the working set of instruction cache
lines drops significantly during sustained parsing.

### 5.2 LLVM `#[cold]` semantics

The `#[cold]` attribute on `parse_<Cat>_cold()` provides two hints to LLVM:

1. **Section placement.**  LLVM places `#[cold]` functions in the
   `.text.unlikely` section (on ELF targets), separating them from hot code
   in `.text.hot`.  This prevents cold code from sharing cache lines with hot
   code at the binary layout level.

2. **Branch weight inference.**  At the call site in `parse_<Cat>()`, the
   wildcard arm `_ => parse_<Cat>_cold(tokens, pos, min_bp)` is the branch
   target leading to a `#[cold]` function.  LLVM infers that this branch is
   unlikely and optimizes the hot arms' fall-through path accordingly.

The `#[inline(never)]` attribute prevents LLVM from re-inlining the cold
helper back into the hot function, which would defeat the purpose of the split.

### 5.3 Branch prediction benefit

With the split, the hot function's `match` expression has fewer arms, which
means:

- Fewer indirect branch targets in the BTB for the match dispatch.
- The wildcard arm (`_ => parse_<Cat>_cold(...)`) is a single, stable
  branch target that the predictor can learn as "not taken" for hot tokens.
- Hot arm branch targets are spatially closer together, improving BTB
  locality.

### 5.4 Data flow diagram

```
┌──────────────────────────────────────────────────┐
│              parse_Bool()                        │
│              (.text.hot section)                 │
│                                                  │
│  match &tokens[*pos].0 {                         │
│      Token::Integer(_) => { ... }  ──── w=0.0    │  ◄── 85% of dispatches
│      Token::KwTrue     => { ... }  ──── w=0.0    │      hit these arms
│      Token::KwFalse    => { ... }  ──── w=0.0    │
│      Token::Ident(_)   => { ... }  ──── w=0.5    │
│      _                 => ───────────────────────┈─┐
│  }                                               │ │
└──────────────────────────────────────────────────┘ │
                                                     │ call (rarely taken)
                          ┌──────────────────────────┘
                          │
                          ▼
┌──────────────────────────────────────────────────┐
│         parse_Bool_cold()                        │
│         (.text.unlikely section)                 │
│         #[cold] #[inline(never)]                 │
│                                                  │
│  match &tokens[*pos].0 {                         │
│      Token::LParen => { ... }  ──── w=1.0        │  ◄── 15% of dispatches
│      _             => parse_Bool_own(...)        │      (loaded on demand)
│  }                                               │
└──────────────────────────────────────────────────┘
```

---

## 6. Interaction with NFA Merged Arms

### 6.1 Scope of A2

The hot/cold splitting in A2 applies exclusively to the **cross-category
dispatch wrapper** `parse_<Cat>()` generated by `write_category_dispatch()` in
`dispatch.rs`.  This function handles:

- Cross-category infix rules (e.g., `Int "==" Int -> Bool`)
- Cast rules (e.g., `Int -> Proc`)
- The wildcard fallback to `parse_<Cat>_own()`

### 6.2 NFA merged arms live elsewhere

NFA-ambiguous prefix dispatching -- where multiple rules share the same
dispatch token (e.g., `float(x)` could be `IntToFloat`, `BoolToFloat`,
`StrToFloat`, or `FloatId`) -- is handled in a different code path:

- **Trampolined parser:** `write_nfa_merged_prefix_arm()` in `trampoline.rs`
  emits the merged arm inside `parse_<Cat>_own()`, not in the dispatch wrapper.
- **Lazy parser:** `group_rd_by_dispatch_token()` groups rules for NFA-style
  try-all parsing inside the Pratt prefix handler.
- **Pratt prefix handler:** `pratt.rs` handles NFA merged prefix arms in the
  Pratt `parse_prefix_<Cat>()` function.

Since NFA merged arms appear in `parse_<Cat>_own()` (called by the dispatch
wrapper's fallback), they are **not affected** by the hot/cold split in A2.
The split operates one level above, deciding which tokens route to the
cross-category path versus the own-category path.

### 6.3 Weight interaction

NFA-ambiguous categories do have dispatch arms with weight >= 0.5 (Cast and
backtracking CrossCategory actions), but these weights are for the
cross-category dispatch layer, not the intra-category NFA disambiguation.
The NFA alternative ordering uses `nfa_alternative_order()` in `wfst.rs`,
which returns indices sorted by WFST weight for the trampoline to try
alternatives in weight-best-first order -- an orthogonal mechanism to A2.

```
  parse_Bool()          ◄── A2 hot/cold split applies here
      │
      ├── hot arms (cross-cat, cast)
      └── _ => parse_Bool_cold()
                  │
                  ├── cold arms (lookahead, variable)
                  └── _ => parse_Bool_own()
                                │
                                ├── Pratt prefix match
                                │     └── NFA merged arms  ◄── nfa_alternative_order()
                                └── Pratt infix loop            (orthogonal to A2)
```

---

## 7. Correctness

### 7.1 Semantic preservation

The hot/cold split is a pure code motion transformation.  The set of match arms
is unchanged; only their physical location in the generated code differs.

**Claim:** For any input token sequence `T` and any category `C`, the split
version produces the same parse result as the unsplit version.

**Proof sketch:**

Let `arms = [a_0, a_1, ..., a_{n-1}]` be the sorted dispatch arms (by weight).
Let `k` be the cold start index (`cold_start_idx`).

- **Case 1: `has_split = false`.**  No transformation occurs.  The generated
  code is identical to the unsplit version.  Trivially correct.

- **Case 2: `has_split = true`.**  The arms are partitioned into
  `hot = arms[0..k)` and `cold = arms[k..n)`.

  For a token `t` at position `*pos`:

  - If `t` matches some arm `a_i` with `i < k`:  The hot function's match
    expression handles `t` directly.  The cold function is never called.
    Same result as the unsplit version where `a_i` would also be the first
    matching arm (since arms are sorted and pattern matching is
    first-match).

  - If `t` matches some arm `a_j` with `j >= k`:  The hot function's
    wildcard routes to `parse_<Cat>_cold()`, which matches `t` against the
    cold arms.  `a_j` is the first matching cold arm.  Same result as the
    unsplit version.

  - If `t` matches no arm:  The hot function's wildcard routes to
    `parse_<Cat>_cold()`, whose wildcard routes to `parse_<Cat>_own()`.
    Same result as the unsplit version's wildcard routing to
    `parse_<Cat>_own()`.

### 7.2 Deterministic token matching

Each token matches at most one arm in the dispatch.  The dispatch arms are
constructed from FIRST-set analysis, which ensures:

- **Cross-category deterministic arms:** Each `(source_category, token)` pair
  produces exactly one arm.  The token is unique to the source category's
  FIRST set (not in the target category's FIRST set).

- **Cross-category ambiguous arms:** Each ambiguous token produces at most one
  arm per category (the WFST-best resolution via composed dispatch, or a
  save/restore arm that falls back to `parse_<Cat>_own()`).

- **Cast arms:** Each token unique to the source category's FIRST set
  produces exactly one arm.

Since the match patterns are non-overlapping, the order of arms within hot or
cold does not affect which arm matches.  The weight-based sort determines the
`match` arm order, which Rust evaluates top-to-bottom (first match wins), but
since patterns are non-overlapping, any ordering produces the same result.

### 7.3 Fallback chain

The fallback chain is extended by one step:

```
  Unsplit:  parse_<Cat>() -> wildcard -> parse_<Cat>_own()
  Split:    parse_<Cat>() -> wildcard -> parse_<Cat>_cold() -> wildcard -> parse_<Cat>_own()
```

The cold helper's wildcard arm explicitly calls `parse_<Cat>_own()`,
preserving the original semantics.  No tokens are lost between the two
levels of dispatch.

---

## 8. Source References

### Implementation

| Symbol                      | File          | Lines    | Description                                         |
|-----------------------------|---------------|----------|-----------------------------------------------------|
| `write_category_dispatch()` | `dispatch.rs` | 63--414  | Dispatch codegen with hot/cold partition            |
| `COLD_THRESHOLD`            | `dispatch.rs` | 320      | Partition threshold constant (1.0)                  |
| `cold_start_idx`            | `dispatch.rs` | 322--324 | Binary search for first cold arm                    |
| `has_split`                 | `dispatch.rs` | 328--329 | Guard: split only when both hot and cold exist      |
| `parse_<Cat>_cold` emission | `dispatch.rs` | 339--354 | Cold helper codegen with `#[cold] #[inline(never)]` |
| `parse_<Cat>` hot emission  | `dispatch.rs` | 357--383 | Hot function codegen with wildcard -> cold          |

### Weight Assignment

| Symbol                                    | File      | Lines    | Description                            |
|-------------------------------------------|-----------|----------|----------------------------------------|
| `compute_action_weight()`                 | `wfst.rs` | 559--581 | Dispatch action -> tropical weight     |
| `PredictionWfst::predict()`               | `wfst.rs` | 139--156 | Weight-sorted action query             |
| `PredictionWfst::nfa_alternative_order()` | `wfst.rs` | 198--230 | NFA weight ordering (orthogonal to A2) |

### Related Subsystems

| Symbol                          | File            | Description                            |
|---------------------------------|-----------------|----------------------------------------|
| `write_nfa_merged_prefix_arm()` | `trampoline.rs` | NFA merged arms (not affected by A2)   |
| `group_rd_by_dispatch_token()`  | `trampoline.rs` | NFA grouping for prefix dispatch       |
| `categories_needing_dispatch()` | `dispatch.rs`   | Which categories get dispatch wrappers |
| `test_compute_action_weight()`  | `wfst.rs`       | Weight assignment unit tests           |
