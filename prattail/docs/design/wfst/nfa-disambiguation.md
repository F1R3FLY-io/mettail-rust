# NFA Disambiguation x WFST Pipeline

**Date:** 2026-03-01

---

## Table of Contents

1. [Problem](#1-problem)
2. [Formal Definition](#2-formal-definition)
3. [Architecture](#3-architecture)
4. [Data Flow](#4-data-flow)
5. [Weight Ordering](#5-weight-ordering)
6. [Spillover Protocol](#6-spillover-protocol)
7. [Forced-Prefix Replay](#7-forced-prefix-replay)
8. [Zero-Overhead Property](#8-zero-overhead-property)
9. [Worked Example](#9-worked-example)
10. [Correctness](#10-correctness)
11. [Complexity](#11-complexity)
12. [Source References](#12-source-references)

---

## 1. Problem

When multiple recursive descent (RD) rules within the same grammar category
share the same dispatch token, the parser cannot select a single rule from the
first token alone. This is the *intra-category ambiguity problem*.

**Concrete instance.** In the Calculator grammar, the `Float` category
contains four cast/identity rules that all begin with the keyword `float`:

```
Float category rules starting with "float(":
  FloatId     . a:Float  |- "float" "(" a ")"  : Float
  IntToFloat  . a:Int    |- "float" "(" a ")"  : Float
  BoolToFloat . a:Bool   |- "float" "(" a ")"  : Float
  StrToFloat  . a:Str    |- "float" "(" a ")"  : Float
```

All four rules share the first terminal `"float"`, the second terminal `"("`,
and the closing delimiter `")"`. They differ only in the *type of the inner
expression* -- and that type is determined by recursive parsing, not by
inspecting the next token. The FIRST sets of `Int`, `Float`, `Bool`, and `Str`
all include `Ident` (any variable name can belong to any type), so two-token
lookahead does not help:

| Token     | Candidate Rules                                  | Decision           |
|-----------|--------------------------------------------------|--------------------|
| `KwFloat` | `FloatId`, `IntToFloat`, `BoolToFloat`, `StrToFloat` | AMBIGUOUS (4-way) |

Before the NFA disambiguation pipeline, this ambiguity triggered a compile-time
`AmbiguousPrefix` warning but was never resolved -- the parser would
arbitrarily try one rule and silently discard the others. The NFA
disambiguation pipeline introduces a structured mechanism to:

1. **Try all** candidate rules for the ambiguous token.
2. **Rank** alternatives by WFST tropical weight (lowest = most likely).
3. **Prune** low-likelihood alternatives via compile-time beam filtering.
4. **Spill** remaining alternatives for forced-prefix replay when semantic
   disambiguation (Layer 6) is needed.
5. **Resolve** among multiple accepting (ground) alternatives using
   weight-aware tiebreaking.

---

## 2. Formal Definition

### 2.1 Tropical Semiring

The weight domain is the tropical semiring T = (R+ union {+inf}, min, +, +inf, 0.0):

| Operation | Symbol | Definition         | Interpretation             |
|-----------|--------|--------------------|----------------------------|
| Plus      | a ⊕ b  | min(a, b)          | Select best alternative    |
| Times     | a ⊗ b  | a + b              | Accumulate cost along path |
| Zero      | 0̄      | +∞                 | Unreachable                |
| One       | 1̄      | 0.0                | Zero cost (deterministic)  |

The ordering `a < b` means "a is more likely than b" (lower weight = higher
priority). The tropical semiring satisfies the required semiring axioms --
see [semirings.md](../../theory/wfst/semirings.md) for the full algebraic
specification and proofs.

### 2.2 NFA Dispatch Model

Let C be a grammar category with rules R = {r_1, ..., r_n}. Let
tau: R --> T be the token dispatch function that maps each rule to its first
terminal. A *dispatch group* for token t is the set:

  G(t) = { r in R : tau(r) = t }

When |G(t)| > 1, the group G(t) is *NFA-ambiguous* -- multiple rules compete
for the same dispatch token. The NFA disambiguation pipeline resolves G(t) by:

1. Assigning weights w: G(t) --> T via the prediction WFST.
2. Sorting alternatives by weight: w(r_i1) <= w(r_i2) <= ... <= w(r_ik).
3. Trying each alternative in weight order, collecting results.
4. Returning the weight-best success as the primary result.
5. Spilling position-matching alternatives for Layer 6 replay.

### 2.3 Beam Pruning Predicate

Given beam width beta in T and best weight w* = min{w(r) : r in G(t)}, the
compile-time beam predicate is:

  P_beam(r) = (w(r) <= w* ⊗ beta)  =  (w(r) <= w* + beta)

Alternatives where P_beam(r) = false are *pruned* -- they are never emitted in
the generated code. This is a compile-time decision; no runtime beam check
appears in the generated NFA merged arm.

### 2.4 Spillover Predicate

At runtime, after all alternatives have been tried, the spillover predicate
selects which N-1 alternatives to spill for forced-prefix replay:

  P_spill(r_i, r_best) = (pos(r_i) == pos(r_best))  AND  P_beam(r_i)

Only alternatives that consumed the *same number of tokens* as the primary
result are spilled. This position filter ensures that the infix loop starts
at the correct token during forced-prefix replay.

---

## 3. Architecture

The NFA disambiguation pipeline spans compile time and runtime, coordinated
through four thread-local storage cells per category.

### 3.1 Thread-Local Storage Cells

For each category `Cat`, four `Cell`-based thread-local variables are emitted
in the generated code:

| Thread-Local                   | Type                             | Purpose                                             |
|--------------------------------|----------------------------------|------------------------------------------------------|
| `NFA_PREFIX_SPILL_CAT`         | `Cell<Vec<(Cat, usize, f64)>>`   | Spillover buffer for N-1 alternatives with weights   |
| `NFA_FORCED_PREFIX_CAT`        | `Cell<Option<(Cat, usize, f64)>>`| Forced-prefix replay override                        |
| `NFA_PRIMARY_WEIGHT_CAT`       | `Cell<f64>`                      | Weight of the primary (best) NFA result              |
| `RUNNING_WEIGHT_CAT`           | `Cell<f64>`                      | Accumulated dispatch confidence weight (B2 adaptive) |

All four use `Cell` (not `RefCell`) because the trampoline's standalone parse
functions may cause re-entrant calls. `Cell::take()` and `Cell::set()` are
safe under re-entrancy -- `Cell::take()` on an empty `Vec` is a pointer swap,
and `Cell::set()` on a default `f64` is a register-width write.

**Generated declaration** (`trampoline.rs:1160-1173`):

```rust
thread_local! {
    static NFA_PREFIX_SPILL_FLOAT: std::cell::Cell<Vec<(Float, usize, f64)>> =
        std::cell::Cell::new(Vec::new());
    static NFA_FORCED_PREFIX_FLOAT: std::cell::Cell<Option<(Float, usize, f64)>> =
        std::cell::Cell::new(None);
    static NFA_PRIMARY_WEIGHT_FLOAT: std::cell::Cell<f64> =
        std::cell::Cell::new(0.5);
    static RUNNING_WEIGHT_FLOAT: std::cell::Cell<f64> =
        std::cell::Cell::new(0.0);
}
```

A fifth thread-local, `AMBIGUOUS_WEIGHTS`, is emitted once per language (not
per category) and carries the weight vector from `parse_preserving_vars` to
`from_alternatives`:

```rust
thread_local! {
    static AMBIGUOUS_WEIGHTS: std::cell::Cell<Vec<f64>> =
        std::cell::Cell::new(Vec::new());
}
```

### 3.2 Compile-Time vs Runtime Boundary

```
  ┌───────────────────────────────────────────────────────────────────────┐
  │  COMPILE TIME (PraTTaIL pipeline)                                     │
  │                                                                       │
  │  ┌─────────────────────────────────────────────────────────────────┐  │
  │  │  Detection                                                      │  │
  │  │    categories_needing_nfa_spillover()                            │  │
  │  │    group_rd_by_dispatch_token()                                  │  │
  │  │    --> needs_nfa_spillover flag on TrampolineConfig               │  │
  │  └─────────────────────────────────────────────────────────────────┘  │
  │                               │                                       │
  │  ┌─────────────────────────────▼───────────────────────────────────┐  │
  │  │  Weight Ordering                                                │  │
  │  │    nfa_alternative_order() --> sorted (index, TropicalWeight)    │  │
  │  │    beam pruning: w(r) <= w* + beta                              │  │
  │  └─────────────────────────────────────────────────────────────────┘  │
  │                               │                                       │
  │  ┌─────────────────────────────▼───────────────────────────────────┐  │
  │  │  Code Generation                                                │  │
  │  │    write_nfa_merged_prefix_arm() --> NFA try-all match arm      │  │
  │  │    write_nfa_inline_constructor() --> Ok(Cat::Label(...))        │  │
  │  │    Thread-local declarations (4 per category)                    │  │
  │  │    Forced-prefix check at top of 'prefix block                  │  │
  │  └─────────────────────────────────────────────────────────────────┘  │
  │                                                                       │
  └───────────────────────────────────────────────────────────────────────┘

  ┌───────────────────────────────────────────────────────────────────────┐
  │  RUNTIME (generated code)                                             │
  │                                                                       │
  │  ┌─────────────────────────────────────────────────────────────────┐  │
  │  │  NFA Merged Arm                                                 │  │
  │  │    Save pos --> try each alternative in weight order              │  │
  │  │    Collect (result, position, weight) for each success           │  │
  │  │    Return best (index 0) --> spill rest to NFA_PREFIX_SPILL      │  │
  │  └─────────────────────────────────────────────────────────────────┘  │
  │                               │                                       │
  │  ┌─────────────────────────────▼───────────────────────────────────┐  │
  │  │  parse_preserving_vars Drain Loop                               │  │
  │  │    Primary parse --> record NFA_PRIMARY_WEIGHT                   │  │
  │  │    Drain NFA_PREFIX_SPILL --> forced-prefix replay               │  │
  │  │    Each replay: set NFA_FORCED_PREFIX --> Cat::parse(input)      │  │
  │  │    Collect successes + weights                                   │  │
  │  └─────────────────────────────────────────────────────────────────┘  │
  │                               │                                       │
  │  ┌─────────────────────────────▼───────────────────────────────────┐  │
  │  │  Weight-Aware from_alternatives                                 │  │
  │  │    AMBIGUOUS_WEIGHTS carries weights parallel to flat            │  │
  │  │    Multiple accepting --> min-weight (tropical) wins             │  │
  │  │    Length mismatch --> first accepting (declaration order)        │  │
  │  └─────────────────────────────────────────────────────────────────┘  │
  │                                                                       │
  └───────────────────────────────────────────────────────────────────────┘
```

---

## 4. Data Flow

The data flow is a six-stage pipeline. Each stage transforms and narrows the
set of alternatives.

### 4.1 Pipeline Stages

```
  Stage 1        Stage 2           Stage 3          Stage 4
  Detection  --> Weight Order  --> Code Gen     --> Runtime Try-All
  |G(t)| > 1     sort by w(r)     emit closure      save/restore
                  beam prune       per alt           collect results
                                                          │
                ┌─────────────────────────────────────────┘
                │
                v
  Stage 5                    Stage 6
  Spillover + Replay     --> Weight-Aware Resolution
  drain NFA_PREFIX_SPILL     from_alternatives
  forced-prefix re-parse     AMBIGUOUS_WEIGHTS tiebreak
  collect (term, weight)     ground-term selection
```

### 4.2 Stage-by-Stage Pseudocode

**Stage 1: Detection** (`trampoline.rs:group_rd_by_dispatch_token`,
`trampoline.rs:categories_needing_nfa_spillover`)

```
group_rd_by_dispatch_token(rd_rules, cat):
    groups = BTreeMap<String, Vec<RDRuleInfo>>
    for rule in rd_rules where rule.category == cat:
        skip if is_simple_collection(rule)
        skip if rule.prefix_bp.is_some()          // unary prefix
        skip if starts_with_nonterminal(rule)      // cross-category
        variant = terminal_to_variant_name(rule.items[0])
        groups[variant].push(rule)
    return groups

categories_needing_nfa_spillover(rd_rules, categories):
    result = HashSet<String>
    for cat in categories:
        groups = group_rd_by_dispatch_token(rd_rules, cat)
        if any group g where |g| > 1:
            result.insert(cat)
    return result
```

**Stage 2: Weight Ordering** (`wfst.rs:nfa_alternative_order`)

```
nfa_alternative_order(token_name, rule_labels):
    predictions = predict(token_name)       // sorted by tropical weight
    indexed = []
    for (i, label) in enumerate(rule_labels):
        w = predictions.find(label).weight   // default 0.5 if not found
        indexed.push((i, w))
    sort indexed by w ascending
    return indexed
```

**Stage 3: Code Generation** (`trampoline.rs:write_nfa_merged_prefix_arm`)

```
write_nfa_merged_prefix_arm(variant, inlineable, cat, config):
    ordered = nfa_alternative_order(variant, inlineable.labels)
    beam = config.prediction_wfst.beam_width()
    best_w = ordered[0].weight

    // Beam prune (compile-time)
    filtered = ordered.filter(|(_, w)| w <= best_w + beam)

    emit: "Token::{variant} => {"
    emit: "  let nfa_saved = *pos;"
    emit: "  let mut nfa_results: Vec<Cat> = Vec::new();"
    emit: "  let mut nfa_positions: Vec<usize> = Vec::new();"
    emit: "  let mut nfa_weights: Vec<f64> = Vec::new();"
    emit: "  let mut nfa_first_err: Option<ParseError> = None;"

    for (idx, (rule, weight)) in filtered:
        emit: "  *pos = nfa_saved;"
        emit: "  match (|| -> Result<Cat, ParseError> {"
        emit: "      // ... parse rule's terminals + cross-cat NTs ..."
        emit: "      Ok(Cat::Label(...))"
        emit: "  })() {"
        emit: "      Ok(v) => { nfa_results.push(v);"
        emit: "                  nfa_positions.push(*pos);"
        emit: "                  nfa_weights.push({weight}); },"
        emit: "      Err(e) => { if nfa_first_err.is_none()"
        emit: "                  { nfa_first_err = Some(e); } },"
        emit: "  }"

    emit: "  match nfa_results.len() {"
    emit: "      0 => return Err(nfa_first_err...),"
    emit: "      _ => {"
    emit: "          *pos = nfa_positions[0];"
    emit: "          let best = nfa_results.remove(0);"
    emit: "          NFA_PRIMARY_WEIGHT_CAT.set(nfa_weights[0]);"
    emit: "          RUNNING_WEIGHT_CAT.set(... + nfa_weights[0]);"
    emit: "          // spill position-matching alternatives"
    emit: "          NFA_PREFIX_SPILL_CAT.set(spill_buf);"
    emit: "          break 'prefix best;"
    emit: "      },"
    emit: "  }"
    emit: "},"
```

**Stage 4: Runtime Try-All** (generated code, inside `parse_Cat_impl`)

Each alternative is wrapped in a closure `(|| -> Result<Cat, ParseError> { ... })()`
so that early returns from `expect_token` and recursive `parse_Cat` calls are
captured as `Err` without aborting the outer NFA loop.

**Stage 5: Spillover and Replay** (`language.rs:1116-1161`)

```
parse_preserving_vars(input):
    successes = []
    success_weights = []
    first_err = None

    for cat in parse_order:
        match Cat::parse(input):
            Ok(term):
                successes.push(TermInner::Cat(term))
                w = NFA_PRIMARY_WEIGHT_CAT.take()   // read + reset to 0.5
                success_weights.push(w)

                spilled = NFA_PREFIX_SPILL_CAT.take()
                for (alt_prefix, alt_pos, alt_weight) in spilled:
                    NFA_FORCED_PREFIX_CAT.set(Some((alt_prefix, alt_pos, alt_weight)))
                    match Cat::parse(input):
                        Ok(alt_term):
                            successes.push(TermInner::Cat(alt_term))
                            success_weights.push(alt_weight)
                        Err(_): ()   // silently discard
                    NFA_PREFIX_SPILL_CAT.take()  // clear nested spillover

            Err(e):
                NFA_PREFIX_SPILL_CAT.take()   // prevent leaking
                if first_err is None: first_err = Some(e)

    AMBIGUOUS_WEIGHTS.set(success_weights)
    match successes.len():
        0 --> Err(first_err)
        1 --> Ok(Term(successes[0]))
        _ --> Ok(Term(from_alternatives(successes)))
```

**Stage 6: Weight-Aware Resolution** (`language.rs:284-326`)

```
from_alternatives(alts):
    n_alts = alts.len()
    flat = flatten(alts)              // unwrap nested Ambiguous

    match flat.len():
        0 --> panic
        1 --> return flat[0]
        _ -->
            accepting = flat.filter(is_accepting)   // ground terms only
            match accepting.len():
                0 --> Ambiguous(flat)                // defer to substitution
                1 --> accepting[0]                   // unambiguous ground
                n where n > 1 -->
                    weights = AMBIGUOUS_WEIGHTS.take()
                    if weights.len() == n_alts AND flat.len() == n_alts:
                        // parallel length invariant holds
                        best_idx = accepting.min_by(|(i,_),(j,_)|
                            weights[i].partial_cmp(&weights[j]))
                        return flat[best_idx]
                    else:
                        return accepting[0]  // first-declared fallback
```

---

## 5. Weight Ordering

### 5.1 Weight Assignment

The prediction WFST assigns weights to dispatch actions during pipeline
construction. For NFA-ambiguous groups, `nfa_alternative_order()` in
`wfst.rs:198-218` queries the WFST for the shared dispatch token and maps
each rule label to its weight:

```
nfa_alternative_order("KwFloat", ["FloatId", "IntToFloat", "BoolToFloat", "StrToFloat"]):

    WFST predictions for KwFloat:
        FloatId     --> weight 0.50  (identity cast, highest priority)
        IntToFloat  --> weight 1.00  (conversion rule)
        BoolToFloat --> weight 1.50  (conversion rule, lower specificity)
        StrToFloat  --> weight 2.00  (conversion rule, lowest specificity)

    Sorted by weight ascending:
        [(0, 0.50), (1, 1.00), (2, 1.50), (3, 2.00)]
```

Rules not found in the WFST receive a default weight of 0.5 (cast-level
priority).

### 5.2 Weight Semantics

The weight determines three things:

| Semantic Role             | Description                                             |
|---------------------------|---------------------------------------------------------|
| **Try order**             | Lowest-weight alternative is tried first                |
| **Primary selection**     | Index 0 after weight-sort is returned as primary result |
| **Tiebreaking**           | Weight carried through spillover for `from_alternatives`|

### 5.3 F2 Early Termination

When the first alternative has weight 0.0 (the tropical multiplicative
identity, meaning "deterministic / zero cost") and the category does NOT
require NFA spillover, the generated code wraps remaining alternatives in
`if nfa_results.is_empty() { ... }`. If the weight-0.0 alternative succeeds,
no other alternative is tried.

F2 is **only safe** when `needs_nfa_spillover` is false. When spillover is
needed, all alternatives must be tried because the primary result may not be
ground (e.g., `float(x)` where `x` is a free variable), and Layer 6 needs
the full set of alternatives for disambiguation after variable substitution.

### 5.4 Beam Pruning

Compile-time beam pruning occurs in `write_nfa_merged_prefix_arm()` at
`trampoline.rs:225-242`. Given beam width beta:

```
Alternatives after beam pruning (beta = 1.0):

    FloatId:     0.50  <-- best (w*)
    IntToFloat:  1.00  <= 0.50 + 1.0 = 1.50  --> KEEP
    BoolToFloat: 1.50  <= 1.50                --> KEEP
    StrToFloat:  2.00  >  1.50                --> PRUNED (not emitted)
```

Pruned alternatives never appear in the generated code -- they produce no
closures, no position saves, no weight pushes. This reduces both code size
and runtime iterations.

An additional runtime beam filter (F1) applies during spillover: alternatives
with `alt_w > nfa_weights[0] + beam` are not pushed to the spill buffer, even
if they were kept at compile time. F1 handles cases where the compile-time best
weight was estimated but the runtime primary result has a different weight.

---

## 6. Spillover Protocol

### 6.1 Spillover Tuple Format

Each spilled alternative is a 3-tuple `(Cat, usize, f64)`:

| Field  | Type    | Semantics                                                    |
|--------|---------|--------------------------------------------------------------|
| `.0`   | `Cat`   | Parsed prefix value (e.g., `IntToFloat(IntVar("x"))`)       |
| `.1`   | `usize` | Token position after parsing (end position of the prefix)   |
| `.2`   | `f64`   | WFST tropical weight (lower = more likely)                  |

### 6.2 Position Filter

Only alternatives that consumed the same number of tokens as the primary
result are spilled:

```
nfa_positions = [4, 4, 4, 3]    // 4 alternatives, third consumed fewer tokens
                     ^
                     position mismatch -- NOT spilled
```

This filter is essential for correctness: during forced-prefix replay, `*pos`
is set to the spilled alternative's end position. If the position were wrong,
the infix loop would start at an incorrect token, producing malformed ASTs.

### 6.3 Cell Take/Set Protocol

The spillover buffer uses `Cell<Vec<...>>` with the take/set pattern:

```
// Write spillover (in NFA merged arm)
NFA_PREFIX_SPILL_CAT.with(|cell| {
    let mut spill_buf = cell.take();     // take ownership (replace with empty Vec)
    for (alt, alt_pos, alt_w) in remaining {
        if alt_pos == primary_pos {
            spill_buf.push((alt, alt_pos, alt_w));
        }
    }
    cell.set(spill_buf);                 // put back (may be empty or populated)
});

// Read spillover (in parse_preserving_vars)
let spilled: Vec<(Cat, usize, f64)> = NFA_PREFIX_SPILL_CAT.with(|cell| cell.take());
// After processing, the cell is already empty (take replaced with Vec::new())
```

The take/set pattern is zero-cost for empty containers: taking an empty `Vec`
produces a `Vec::new()` (zero heap allocation), and setting an empty `Vec`
stores a null-pointer-width struct. No `RefCell` borrow tracking overhead is
incurred.

---

## 7. Forced-Prefix Replay

### 7.1 Mechanism

When `parse_preserving_vars` drains the spillover buffer, it replays each
spilled alternative through the full parser (prefix + infix loop) by setting
`NFA_FORCED_PREFIX_CAT` and calling `Cat::parse(input)`:

```
// In parse_preserving_vars (language.rs:1144-1153)
for (alt_prefix, alt_pos, alt_weight) in spilled {
    NFA_FORCED_PREFIX_CAT.with(|cell|
        cell.set(Some((alt_prefix, alt_pos, alt_weight)))
    );
    if let Ok(alt_term) = Cat::parse(input) {
        successes.push(TermInner::Cat(alt_term));
        success_weights.push(alt_weight);
    }
    // Clear nested spillover to prevent cascading
    NFA_PREFIX_SPILL_CAT.with(|cell| { cell.take(); });
}
```

### 7.2 Forced-Prefix Check

At the very top of each category's `'prefix` block, the generated code checks
for a forced-prefix override (`trampoline.rs:1343-1358`):

```rust
// Generated at the top of parse_Float's prefix block
{
    let forced = NFA_FORCED_PREFIX_FLOAT.with(|cell| cell.take());
    if let Some((forced_val, forced_pos, _forced_weight)) = forced {
        *pos = forced_pos;
        break 'prefix forced_val;
    }
}
// ... normal prefix match follows only if no forced prefix was set
```

When the forced-prefix check fires:

1. `*pos` is advanced to `forced_pos` (past the tokens the prefix consumed).
2. `forced_val` becomes `lhs` in the Pratt infix loop.
3. The infix loop runs normally, giving the alternative its correct operator
   context (e.g., `float(x) + 1.0` continues with `+` binding as Float
   addition).

### 7.3 Why Full Replay Is Necessary

A design that only collected prefix values (without running the infix loop)
would lose operator context. Consider `float(x) + 1.0`:

| Approach          | Result                                               | Correct? |
|-------------------|------------------------------------------------------|----------|
| Prefix-only       | `IntToFloat(IntVar("x"))`                           | No -- missing `+ 1.0` |
| Full replay       | `FloatAdd(IntToFloat(IntVar("x")), FloatLit(1.0))`  | Yes      |

The forced-prefix replay runs the *complete* parser (prefix + infix loop),
so each alternative gets its full syntactic context.

### 7.4 Nested Spillover Prevention

During forced-prefix replay, the parser may re-enter the NFA merged arm if
the replay triggers a recursive parse of an NFA-ambiguous category. To prevent
cascading spillover that would corrupt the outer replay loop, the drain code
clears any nested spillover after each replay:

```rust
NFA_PREFIX_SPILL_CAT.with(|cell| { cell.take(); });
```

This ensures that each iteration of the drain loop starts with a clean
spillover buffer.

---

## 8. Zero-Overhead Property

### 8.1 Cost Analysis by Scenario

| Scenario                  | Cost                                                      |
|---------------------------|-----------------------------------------------------------|
| Unambiguous dispatch      | `Cell::take()` on `None` / empty `Vec` (pointer swap)     |
| All alternatives fail     | Single error return, no spillover written                  |
| Single NFA success        | No spillover push (only `break 'prefix best`)             |
| N NFA successes (N >= 2)  | NFA merged arm: N try-restore + spillover push            |
| Spillover replay          | N-1 full re-parses via forced prefix                      |

### 8.2 Why Unambiguous Is Free

The thread-local declarations are emitted for **all** categories (not just
NFA-ambiguous ones) so that `parse_preserving_vars` can unconditionally drain
them without compile-time category branching. The cost when these cells are
never populated:

| Operation                            | Cost               |
|--------------------------------------|--------------------|
| `Cell::take()` on empty `Vec`        | Pointer swap (2 writes) |
| `Cell::take()` on `None`             | Register-width copy     |
| `Cell::get()` on default `f64`       | Register-width read     |
| `Cell::set()` on `f64`              | Register-width write    |

### 8.3 No Thread-Local Access on Non-NFA Arms

Dispatch arms for unambiguous tokens (where |G(t)| = 1) do not touch any NFA
thread-local. They follow the standard trampoline path: consume terminals,
push frames for same-category nonterminals, or `break 'prefix` for fully
inlineable rules. The NFA thread-locals are only accessed in:

1. The NFA merged arm (on NFA-ambiguous tokens).
2. The forced-prefix check (at `'prefix` block entry, but `take()` on `None`
   is free).
3. The `parse_preserving_vars` drain loop (after `Cat::parse` completes).

### 8.4 Cell vs RefCell Justification

`Cell` is chosen over `RefCell` for three reasons:

1. **Re-entrancy safety.** The trampoline's standalone parse functions (for
   ZipMapSep and multi-binder rules) can cause re-entrant calls to the
   parser. `Cell::take()` under re-entrancy produces a fresh empty value;
   `RefCell::borrow()` under re-entrancy panics.
2. **No runtime borrow tracking.** `Cell` has zero bookkeeping overhead --
   no borrow flag, no atomic increment/decrement.
3. **Matching the frame pool pattern.** The thread-local frame pool
   (`FRAME_POOL_CAT`) already uses `Cell<Vec<Frame_Cat>>` with take/set.
   Using the same pattern for NFA spillover keeps the generated code uniform.

---

## 9. Worked Example

### 9.1 Setup

**Grammar:** Calculator with categories `Int`, `Float`, `Bool`, `Str`.

**Input:** `float(x)` where `x` is bound to `Bool(true)` in the environment.

**Goal:** Show the full flow from NFA try-all through forced-prefix replay to
weight-aware resolution.

### 9.2 Step-by-Step Trace

```
Input: "float(x)"
Tokens: [KwFloat, LParen, Ident("x"), RParen, Eof]
Positions:  0       1       2          3       4

Category parse order: [Int, Float, Bool, Str]

================================================================================
STAGE A: Int::parse("float(x)")
================================================================================

  Int prefix: token KwFloat. No Int rule starts with KwFloat.
  --> Err(UnexpectedToken { expected: "Int expression", found: "KwFloat" })
  NFA_PREFIX_SPILL_INT.take() --> empty (clear on error)
  first_err = Some(Err(...))

================================================================================
STAGE B: Float::parse("float(x)")
================================================================================

  Float prefix: token KwFloat.

  ---- Forced-prefix check ----
  NFA_FORCED_PREFIX_FLOAT.take() --> None (no forced prefix)
  --> proceed to normal prefix match

  ---- NFA Merged Arm: KwFloat ----
  nfa_saved = 0

  Alternative 1: FloatId (weight 0.50)
    *pos = 0
    (|| -> Result<Float, ParseError> {
        expect "float": pos = 1
        expect "(":     pos = 2
        parse_Float(tokens, pos=2, min_bp=0):
            Ident("x") --> FloatVar("x"). pos = 3.
        expect ")":     pos = 4
        Ok(Float::FloatId(Box::new(FloatVar("x"))))
    })() --> Ok(FloatId(FloatVar("x")))
    nfa_results.push(FloatId(FloatVar("x")))
    nfa_positions.push(4)
    nfa_weights.push(0.50)

  Alternative 2: IntToFloat (weight 1.00)
    *pos = 0
    (|| -> Result<Float, ParseError> {
        expect "float": pos = 1
        expect "(":     pos = 2
        parse_Int(tokens, pos=2, min_bp=0):
            Ident("x") --> IntVar("x"). pos = 3.
        expect ")":     pos = 4
        Ok(Float::IntToFloat(Box::new(IntVar("x"))))
    })() --> Ok(IntToFloat(IntVar("x")))
    nfa_results.push(IntToFloat(IntVar("x")))
    nfa_positions.push(4)
    nfa_weights.push(1.00)

  Alternative 3: BoolToFloat (weight 1.50)
    *pos = 0
    (|| -> Result<Float, ParseError> {
        expect "float": pos = 1
        expect "(":     pos = 2
        parse_Bool(tokens, pos=2, min_bp=0):
            Ident("x") --> BoolVar("x"). pos = 3.
        expect ")":     pos = 4
        Ok(Float::BoolToFloat(Box::new(BoolVar("x"))))
    })() --> Ok(BoolToFloat(BoolVar("x")))
    nfa_results.push(BoolToFloat(BoolVar("x")))
    nfa_positions.push(4)
    nfa_weights.push(1.50)

  Alternative 4: StrToFloat (weight 2.00)
    *pos = 0
    (|| -> Result<Float, ParseError> {
        expect "float": pos = 1
        expect "(":     pos = 2
        parse_Str(tokens, pos=2, min_bp=0):
            Ident("x") --> StrVar("x"). pos = 3.
        expect ")":     pos = 4
        Ok(Float::StrToFloat(Box::new(StrVar("x"))))
    })() --> Ok(StrToFloat(StrVar("x")))
    nfa_results.push(StrToFloat(StrVar("x")))
    nfa_positions.push(4)
    nfa_weights.push(2.00)

  ---- Result Selection ----
  nfa_results.len() = 4 (> 0)

  *pos = nfa_positions[0] = 4
  best = FloatId(FloatVar("x"))       // index 0, lowest weight

  NFA_PRIMARY_WEIGHT_FLOAT.set(0.50)
  RUNNING_WEIGHT_FLOAT.set(0.0 + 0.50 = 0.50)

  Spillover (position filter: all have pos == 4):
    spill_buf = [
        (IntToFloat(IntVar("x")),   4, 1.00),
        (BoolToFloat(BoolVar("x")), 4, 1.50),
        (StrToFloat(StrVar("x")),   4, 2.00),
    ]
  NFA_PREFIX_SPILL_FLOAT.set(spill_buf)

  break 'prefix FloatId(FloatVar("x"))

  ---- Infix Loop ----
  lhs = FloatId(FloatVar("x")), pos = 4
  Token at pos 4: Eof. No infix operator binds.
  --> break infix loop.

  Float::parse returns Ok(FloatId(FloatVar("x")))

================================================================================
STAGE C: parse_preserving_vars drain (Float category)
================================================================================

  successes = [TermInner::Float(FloatId(FloatVar("x")))]
  w = NFA_PRIMARY_WEIGHT_FLOAT.take() = 0.50
  success_weights = [0.50]

  spilled = NFA_PREFIX_SPILL_FLOAT.take() = [
      (IntToFloat(IntVar("x")),   4, 1.00),
      (BoolToFloat(BoolVar("x")), 4, 1.50),
      (StrToFloat(StrVar("x")),   4, 2.00),
  ]

  ---- Replay 1: IntToFloat(IntVar("x")), weight 1.00 ----
  NFA_FORCED_PREFIX_FLOAT.set(Some((IntToFloat(IntVar("x")), 4, 1.00)))
  Float::parse("float(x)"):
      Forced-prefix check: take --> Some((IntToFloat(IntVar("x")), 4, _))
      *pos = 4. break 'prefix IntToFloat(IntVar("x"))
      Infix loop: Eof --> break.
  --> Ok(IntToFloat(IntVar("x")))
  successes.push(TermInner::Float(IntToFloat(IntVar("x"))))
  success_weights.push(1.00)
  NFA_PREFIX_SPILL_FLOAT.take() --> empty (clear nested)

  ---- Replay 2: BoolToFloat(BoolVar("x")), weight 1.50 ----
  NFA_FORCED_PREFIX_FLOAT.set(Some((BoolToFloat(BoolVar("x")), 4, 1.50)))
  Float::parse("float(x)"):
      Forced-prefix check: take --> Some((BoolToFloat(BoolVar("x")), 4, _))
      *pos = 4. break 'prefix BoolToFloat(BoolVar("x"))
      Infix loop: Eof --> break.
  --> Ok(BoolToFloat(BoolVar("x")))
  successes.push(TermInner::Float(BoolToFloat(BoolVar("x"))))
  success_weights.push(1.50)
  NFA_PREFIX_SPILL_FLOAT.take() --> empty (clear nested)

  ---- Replay 3: StrToFloat(StrVar("x")), weight 2.00 ----
  NFA_FORCED_PREFIX_FLOAT.set(Some((StrToFloat(StrVar("x")), 4, 2.00)))
  Float::parse("float(x)"):
      Forced-prefix check: take --> Some((StrToFloat(StrVar("x")), 4, _))
      *pos = 4. break 'prefix StrToFloat(StrVar("x"))
      Infix loop: Eof --> break.
  --> Ok(StrToFloat(StrVar("x")))
  successes.push(TermInner::Float(StrToFloat(StrVar("x"))))
  success_weights.push(2.00)
  NFA_PREFIX_SPILL_FLOAT.take() --> empty (clear nested)

================================================================================
STAGE D: Bool::parse, Str::parse ("float(x)")
================================================================================

  Bool::parse: KwFloat not in Bool's first set --> Err(...)
  Str::parse:  KwFloat not in Str's first set  --> Err(...)

================================================================================
STAGE E: from_alternatives with AMBIGUOUS_WEIGHTS
================================================================================

  successes (all Float category, 4 alternatives):
    [0] FloatId(FloatVar("x"))        weight 0.50
    [1] IntToFloat(IntVar("x"))       weight 1.00
    [2] BoolToFloat(BoolVar("x"))     weight 1.50
    [3] StrToFloat(StrVar("x"))       weight 2.00

  n_alts = 4
  flat (no nested Ambiguous) = successes  (len 4)

  accepting = flat.filter(is_accepting)
    All 4 contain free variables (FVar, IVar, BVar, SVar) --> not ground.
    accepting.len() = 0

  --> Ambiguous([FloatId(FloatVar("x")),
                 IntToFloat(IntVar("x")),
                 BoolToFloat(BoolVar("x")),
                 StrToFloat(StrVar("x"))])

================================================================================
STAGE F: substitute_env (x = Bool(true))
================================================================================

  Environment: { "x" --> Bool(true) }

  Substitute each alternative:
    FloatId(FloatVar("x"))        --> FloatId(FloatVar("x"))       (no progress, x not Float)
    IntToFloat(IntVar("x"))       --> IntToFloat(IntVar("x"))      (no progress, x not Int)
    BoolToFloat(BoolVar("x"))     --> BoolToFloat(Bool(true))      (PROGRESS! x is Bool)
    StrToFloat(StrVar("x"))       --> StrToFloat(StrVar("x"))      (no progress, x not Str)

  Progressed = [BoolToFloat(Bool(true))]
  Dedup = [BoolToFloat(Bool(true))]

  from_alternatives([BoolToFloat(Bool(true))])
    flat.len() = 1 --> return BoolToFloat(Bool(true))

  FINAL RESULT: Float(BoolToFloat(Bool(true)))
```

### 9.3 Diagram: Data Flow Through Thread-Locals

```
  parse_Float('prefix block)
  ┌──────────────────────────────────────────────────────────────────┐
  │ NFA merged arm (KwFloat)                                         │
  │                                                                  │
  │  FloatId ──┐                                                     │
  │  IntToFloat──┤  nfa_results = [R0, R1, R2, R3]                   │
  │  BoolToFloat─┤  nfa_weights = [0.50, 1.00, 1.50, 2.00]          │
  │  StrToFloat──┘                                                   │
  │                                                                  │
  │  best = R0 (FloatId)                                             │
  │  spill = [(R1,4,1.0), (R2,4,1.5), (R3,4,2.0)]                  │
  │          │                │                                      │
  └──────────┼────────────────┼──────────────────────────────────────┘
             │                │
             │  ┌─────────────▼──────────────────────────────┐
             │  │ NFA_PREFIX_SPILL_FLOAT                      │
             │  │   Cell<Vec<(Float, usize, f64)>>            │
             │  └─────────────┬──────────────────────────────┘
             │                │
             │  ┌─────────────▼──────────────────────────────┐
             │  │ NFA_PRIMARY_WEIGHT_FLOAT                    │
             │  │   Cell<f64> = 0.50                          │
             │  └─────────────┬──────────────────────────────┘
             │                │
  ┌──────────▼────────────────▼──────────────────────────────────────┐
  │ parse_preserving_vars                                             │
  │                                                                   │
  │  primary: Ok(FloatId(FloatVar("x")))     weight: 0.50            │
  │                                                                   │
  │  drain spill:                                                     │
  │    ┌────────────────────────────────────────────────────────────┐ │
  │    │ NFA_FORCED_PREFIX_FLOAT.set(R1)  --> Float::parse(input)   │ │
  │    │ NFA_FORCED_PREFIX_FLOAT.set(R2)  --> Float::parse(input)   │ │
  │    │ NFA_FORCED_PREFIX_FLOAT.set(R3)  --> Float::parse(input)   │ │
  │    └────────────────────────────────────────────────────────────┘ │
  │                                                                   │
  │  successes = [R0', R1', R2', R3']    weights = [0.5, 1.0, 1.5, 2.0] │
  │                          │                          │              │
  │                          ▼                          ▼              │
  │                 AMBIGUOUS_WEIGHTS.set(weights)                     │
  │                 from_alternatives(successes)                       │
  └───────────────────────────────────────────────────────────────────┘
```

---

## 10. Correctness

### 10.1 Completeness

**Claim.** Every rule in G(t) that passes the beam predicate P_beam(r) is
tried at runtime.

**Argument.** The compile-time loop in `write_nfa_merged_prefix_arm()` iterates
over `ordered_inlineable`, which contains every rule in G(t) that satisfies
P_beam. Each such rule is emitted as a closure-wrapped try block. At runtime,
the generated code executes all closures sequentially with position reset
between each. No alternative is skipped unless F2 early termination fires --
and F2 is only enabled when `needs_nfa_spillover` is false (meaning no
spillover is needed, so completeness for disambiguation purposes is
irrelevant).

### 10.2 Soundness

**Claim.** The primary result (index 0) is the weight-best alternative, and
all spilled alternatives have weight >= the primary's weight.

**Argument.** `nfa_alternative_order()` sorts by `TropicalWeight::cmp` (total
ordering via `f64::total_cmp`). The sorted indices are iterated in order during
code generation, so `nfa_results[0]` corresponds to the lowest-weight rule.
Spillover iterates `nfa_results[1..]`, all of which have weight >= w(r_0) by
the sort invariant.

### 10.3 Position Consistency

**Claim.** After forced-prefix replay, the infix loop starts at the correct
token position.

**Argument.** Each spilled alternative carries its end position (`alt_pos`)
from the NFA merged arm. The forced-prefix check sets `*pos = forced_pos`
before `break 'prefix forced_val`. Since `forced_pos` was recorded when the
alternative's prefix parse completed, the infix loop begins at exactly the
token where the prefix left off -- the same position it would have started at
had this alternative been the primary result.

### 10.4 Re-Entrancy Safety

**Claim.** `Cell`-based thread-locals are safe under re-entrant parser calls.

**Argument.** `Cell::take()` atomically replaces the cell's value with the
type's default (empty `Vec`, `None`, `0.5`) and returns the previous value.
If a re-entrant call occurs between `take()` and `set()`, the re-entrant
call sees a fresh default value, operates on it independently, and sets its
own result. When the outer call resumes and calls `set()`, it overwrites the
re-entrant call's value -- but this is correct because the outer call's
spillover buffer contains only the outer call's alternatives, not the
re-entrant call's. No aliasing, no double-borrow, no panic.

### 10.5 Parallel Length Invariant

**Claim.** When `weights.len() == n_alts` and `flat.len() == n_alts` in
`from_alternatives`, `weights[i]` corresponds to `flat[i]`.

**Argument.** `n_alts = alts.len()` is captured before flattening.
`weights` has length `n_alts` because `success_weights` has one entry per
`successes.push()` call, and `n_alts` counts exactly those pushes. The
flattened `flat` has length `n_alts` only when no element of `alts` is
`Ambiguous` (no expansion during flattening). The guard
`weights.len() == n_alts && flat.len() == n_alts` ensures the invariant
holds before weight indexing. On violation, the fallback returns the first
accepting alternative (declaration-order determinism).

---

## 11. Complexity

### 11.1 Compile-Time Complexity

| Operation                           | Complexity           | Notes                         |
|-------------------------------------|----------------------|-------------------------------|
| `group_rd_by_dispatch_token`        | O(|R|)               | Single scan of rules          |
| `categories_needing_nfa_spillover`  | O(|C| x |R|)        | Per-category grouping         |
| `nfa_alternative_order`             | O(k log k)           | Sort k alternatives per group |
| Beam pruning                        | O(k)                 | Single filter pass            |
| Code emission                       | O(sum k_i x s_i)     | k_i alts x s_i syntax items  |

Where |R| = total rules, |C| = total categories, k = group size, s = rule
syntax length.

### 11.2 Runtime Complexity

| Scenario                       | Time Complexity              | Space Complexity            |
|--------------------------------|------------------------------|-----------------------------|
| Unambiguous (|G(t)| = 1)      | O(1) extra (Cell::take only) | O(0) (no allocation)        |
| NFA try-all (k alternatives)  | O(k x P(n))                  | O(k) for result vectors     |
| Spillover replay               | O((k-1) x P(n))             | O(k-1) for spill buffer     |
| from_alternatives              | O(k)                         | O(k) for flat vector        |
| Total worst case               | O(k^2 x P(n))               | O(k)                        |

Where P(n) = parse cost for input of length n. The O(k^2) factor arises when
all k alternatives succeed: k tries in the NFA merged arm, then k-1 forced-prefix
replays each running the full parser. In practice, k is small (typically 2-4 for
cast rules sharing a keyword) and P(n) is dominated by the input length, so the
quadratic factor in k is negligible.

### 11.3 Space Overhead

| Component                                | Allocation          | Lifetime         |
|------------------------------------------|---------------------|------------------|
| Thread-locals (4 per category)           | Register-width each | Thread-static    |
| `nfa_results`, `nfa_positions`, `nfa_weights` | O(k) per parse  | Stack (function) |
| Spillover buffer                         | O(k-1) per parse    | Thread-local     |
| `AMBIGUOUS_WEIGHTS`                      | O(N) per parse      | Thread-local     |

Where N = total successes across all categories (typically 1-4).

---

## 12. Source References

| Concept                                | File                                 | Location                                |
|----------------------------------------|--------------------------------------|-----------------------------------------|
| RD rule grouping by dispatch token     | `prattail/src/trampoline.rs`         | `group_rd_by_dispatch_token()` (77-116)  |
| Public wrapper for pipeline access     | `prattail/src/trampoline.rs`         | `group_rd_by_dispatch_token_pub()` (120-125) |
| NFA-ambiguous category detection       | `prattail/src/trampoline.rs`         | `categories_needing_nfa_spillover()` (136-151) |
| NFA merged prefix arm codegen          | `prattail/src/trampoline.rs`         | `write_nfa_merged_prefix_arm()` (162-421) |
| NFA inline constructor                 | `prattail/src/trampoline.rs`         | `write_nfa_inline_constructor()` (428-450+) |
| `TrampolineConfig.needs_nfa_spillover` | `prattail/src/trampoline.rs`         | Lines 726-730                            |
| Thread-local declarations (per-cat)    | `prattail/src/trampoline.rs`         | Lines 1160-1173                          |
| `running_weight_<cat>()` accessor      | `prattail/src/trampoline.rs`         | Lines 1178-1184                          |
| Forced-prefix check (trampoline)       | `prattail/src/trampoline.rs`         | Lines 1343-1358                          |
| Prefix match arm dispatch (NFA merge)  | `prattail/src/trampoline.rs`         | `write_prefix_match_arms()` (1370-1488)  |
| Forced-prefix check (lazy parser)      | `prattail/src/trampoline.rs`         | Lines 3149                               |
| NFA spillover detection in pipeline    | `prattail/src/pipeline.rs`           | Lines 800-840                            |
| `needs_nfa_spillover` configuration    | `prattail/src/pipeline.rs`           | Line 910                                 |
| WFST alternative ordering              | `prattail/src/wfst.rs`              | `nfa_alternative_order()` (198-218)      |
| Beam width query                       | `prattail/src/wfst.rs`              | `PredictionWfst::beam_width()` (226-228) |
| Predict with confidence                | `prattail/src/wfst.rs`              | `predict_with_confidence()` (169-173)    |
| Predict with beam pruning              | `prattail/src/wfst.rs`              | `predict_pruned()` (179-191)             |
| `AMBIGUOUS_WEIGHTS` thread-local       | `macros/src/gen/runtime/language.rs` | Lines 1529-1535                          |
| Drain loop in `parse_preserving_vars`  | `macros/src/gen/runtime/language.rs` | Lines 1116-1161                          |
| Weight-aware `from_alternatives()`     | `macros/src/gen/runtime/language.rs` | Lines 284-326                            |
| `is_accepting()` for ground terms      | `macros/src/gen/runtime/language.rs` | Lines 271-278                            |
| `substitute_env()` for Ambiguous       | `macros/src/gen/runtime/language.rs` | Lines 328-387                            |
| Tropical semiring definition           | `prattail/src/automata/semiring.rs`  | `Semiring` trait (36-51)                 |
| `TropicalWeight` implementation        | `prattail/src/automata/semiring.rs`  | Lines 68-100                             |
| `BeamWidthConfig` enum                 | `prattail/src/lib.rs`               | Lines 76-123                             |

### Cross-References

- [Prediction WFSTs](prediction.md) -- Weight assignment for dispatch actions
- [Semirings](../../theory/wfst/semirings.md) -- Tropical semiring axioms and proofs
- [Semantic Disambiguation (Layer 6)](../disambiguation/07-semantic-disambiguation.md) -- `from_alternatives`, `substitute_env`, groundness
- [NFA Intra-Category Disambiguation (Layer 2.5)](../disambiguation/08-nfa-wfst-disambiguation.md) -- Comprehensive Layer 2.5 reference
- [Dead Rule Detection](dead-rule-detection.md) -- Uses WFST reachability and NFA ambiguity analysis
- [Token Lattices](token-lattices.md) -- Alternative lattice-based disambiguation path
