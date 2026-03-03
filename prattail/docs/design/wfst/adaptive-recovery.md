# Adaptive Recovery via Runtime Weight Accumulation

**Date:** 2026-03-01

---

## Table of Contents

1. [Problem Statement](#1-problem-statement)
2. [Mechanism](#2-mechanism)
3. [Strategy Selection](#3-strategy-selection)
4. [Zero-Overhead Property](#4-zero-overhead-property)
5. [Weight Scale](#5-weight-scale)
6. [Interaction with Frame State](#6-interaction-with-frame-state)
7. [Worked Example](#7-worked-example)
8. [Data Flow Diagram](#8-data-flow-diagram)
9. [Threshold Justification](#9-threshold-justification)
10. [RecoveryConfig Integration](#10-recoveryconfig-integration)
11. [Source Reference](#11-source-reference)

---

## 1. Problem Statement

The WFST error recovery system (documented in
[error-recovery.md](error-recovery.md)) assigns repair costs using static
multipliers drawn from three tiers of context:

| Tier | Signal             | Source                 |
|------|--------------------|------------------------|
| 1    | Frame depth & kind | `FRAME_STATE_CAT`      |
| 2    | Bracket balance    | Incremental bracket counter |
| 3    | Parse simulation   | Forward look-ahead     |

All three tiers reflect *structural* context -- how deep the parser is,
what kind of frame it occupies, and whether a proposed repair leads to
valid continuation.  None of them capture *semantic* context: how
confident the parser was in the dispatch decisions that led to the error
site.

This distinction matters.  Consider two error sites at identical depth
and frame kind:

```
Path A (deterministic):
  Token "x"  → Direct dispatch  (weight 0.0)
  Token ":="  → Direct dispatch  (weight 0.0)
  Token "???"  → ERROR
  running_weight = 0.0

Path B (ambiguous):
  Token "x"  → Cast dispatch     (weight 0.5)
  Token "("  → CrossCategory+BT  (weight 0.5)
  Token "???"  → ERROR
  running_weight = 1.0
```

On path A the parser reached the error through a sequence of
unambiguous, zero-cost dispatch decisions.  The parse prefix is highly
reliable, so the error is almost certainly in the *input*.  Skip to the
nearest structural token is the right strategy: the context before the
error is trustworthy, and we should discard the erroneous fragment.

On path B the parser resolved two ambiguities before encountering the
error.  The accumulated dispatch weight of 1.0 indicates that the parse
prefix itself may be wrong -- the parser may have taken the wrong branch
at an earlier Cast or CrossCategory decision.  In this case, inserting a
missing token to preserve the current parse context is preferable to
skipping, because skip discards context that might still be salvageable
once the correct branch is discovered by replay.

Without a mechanism to distinguish these two cases, the recovery engine
treats both identically, relying solely on structural signals that
happen to be the same.

---

## 2. Mechanism

### 2.1 Thread-Local Accumulator

Each syntactic category receives a thread-local `Cell<f64>` named
`RUNNING_WEIGHT_<CAT>`.  This cell accumulates the tropical weight of
every NFA dispatch decision made during the current parse invocation.

```rust
thread_local! {
    static RUNNING_WEIGHT_PROC: std::cell::Cell<f64> =
        std::cell::Cell::new(0.0);
}
```

The accumulator is initialized to `0.0` at the top of the wrapper
function (`parse_<cat>`), before the trampolined `_impl` function is
entered:

```rust
fn parse_proc<'a>(
    tokens: &[(Token<'a>, Range)],
    pos: &mut usize,
    min_bp: u8,
) -> Result<Proc, ParseError> {
    RUNNING_WEIGHT_PROC.with(|cell| cell.set(0.0));   // B2: reset
    FRAME_POOL_PROC.with(|cell| {
        let mut stack = cell.take();
        // ...
        let result = parse_proc_impl(tokens, pos, min_bp, &mut stack);
        cell.set(stack);
        result
    })
}
```

### 2.2 Accumulation at Dispatch

When an NFA dispatch merges multiple alternatives and selects the
best (lowest-weight) one, the winning weight `nfa_weights[0]` is added
to the running total:

```rust
// Inside NFA merged-arms handler (trampoline prefix dispatch):
_ => {
    *pos = nfa_positions[0];
    NFA_PRIMARY_WEIGHT_PROC.with(|cell| cell.set(nfa_weights[0]));
    RUNNING_WEIGHT_PROC.with(|cell| cell.set(cell.get() + nfa_weights[0]));
    NFA_PREFIX_SPILL_PROC.with(|cell| {
        let mut spill_buf = cell.take();
        for ((alt, &alt_pos), &alt_w) in iter
            .zip(nfa_positions[1..].iter())
            .zip(nfa_weights[1..].iter())
        {
            // beam filter ...
            spill_buf.push((alt, alt_pos, alt_w));
        }
        cell.set(spill_buf);
    });
    break 'prefix best;
},
```

For non-spillover paths (categories without forced-prefix replay), the
accumulation is identical but without the spill buffer logic:

```rust
_ => {
    *pos = nfa_positions[0];
    RUNNING_WEIGHT_PROC.with(|cell| cell.set(cell.get() + nfa_weights[0]));
    break 'prefix nfa_results.into_iter().next()
        .expect("nfa_results non-empty");
},
```

### 2.3 Accessor Function

A generated inline accessor reads the accumulated weight:

```rust
#[inline]
fn running_weight_proc() -> f64 {
    RUNNING_WEIGHT_PROC.with(|cell| cell.get())
}
```

This is used by recovery code and is available for diagnostic purposes.

---

## 3. Strategy Selection

The recovering function reads the accumulated weight immediately after
a parse error is caught:

```rust
fn parse_proc_own_recovering<'a>(
    tokens: &[(Token<'a>, Range)],
    pos: &mut usize,
    min_bp: u8,
    errors: &mut Vec<ParseError>,
) -> Option<Proc> {
    match parse_proc_own(tokens, pos, min_bp) {
        Ok(v) => Some(v),
        Err(e) => {
            let _running_w = RUNNING_WEIGHT_PROC.with(|cell| cell.get());
            errors.push(e);
            sync_to(tokens, pos, &|t| is_sync_proc(t));
            None
        }
    }
}
```

The accumulated weight partitions into two strategy regimes:

| Accumulated Weight | Regime         | Preferred Strategy | Rationale |
|--------------------|----------------|--------------------|-----------|
| < 1.0              | Deterministic  | Skip               | Parse prefix is reliable; discard erroneous input |
| >= 1.0             | Ambiguous      | Insert             | Parse prefix may be wrong; preserve context for replay |

### 3.1 Low Weight (Deterministic) -- Prefer Skip

When the accumulated weight is below the threshold, every dispatch
decision along the path had weight 0.0 (Direct, Grouping, or
non-backtracking CrossCategory).  The parse prefix is essentially
certain.  The most effective repair is to skip past the unexpected
tokens until a sync point is reached, because:

- The context *before* the error is trustworthy and should be preserved.
- The tokens *at* the error site are the problem, not the parse path.
- Skip has the lowest base cost (0.5/token) and finds a valid
  continuation quickly.

### 3.2 High Weight (Ambiguous) -- Prefer Insert

When the accumulated weight equals or exceeds the threshold, the
parser has resolved at least two ambiguous dispatches (each Cast or
backtracking CrossCategory contributes 0.5).  The parse prefix carries
uncertainty:

- The parser *may* have taken a wrong branch at an earlier decision.
- Skipping discards tokens that might be valid under an alternative
  interpretation.
- Inserting a phantom token preserves the current context, allowing
  NFA forced-prefix replay to re-evaluate alternative branches.
- Higher insert cost (2.0 base) is justified because it avoids
  destructive skip when the parse path itself is uncertain.

---

## 4. Zero-Overhead Property

The adaptive recovery mechanism has effectively zero overhead on the
happy path (no parse errors):

| Operation | When | Cost | Frequency |
|-----------|------|------|-----------|
| `Cell::set(0.0)` | Wrapper entry | Atomic pointer store | Once per `parse_<cat>` call |
| `Cell::set(cell.get() + w)` | NFA dispatch | Load + f64 add + store | Once per NFA merged arm |
| `Cell::get()` | Error recovery | Atomic pointer load | Only on parse error |

### 4.1 Why Cell, Not RefCell

`Cell<f64>` uses direct memory operations (`get`/`set`) with no runtime
borrow checking.  For `Copy` types like `f64`, `Cell::get()` is a single
load instruction and `Cell::set()` is a single store.  There is no
`RefCell` overhead (borrow flag check, panic path).

### 4.2 Why Thread-Local, Not Stack Parameter

Passing the running weight as a function parameter through the
trampolined call stack would require:

1. An additional field in every `Frame_<Cat>` variant (increasing frame
   size by 8 bytes).
2. Save/restore logic at every push/pop boundary.
3. Thread-local access patterns already established for `FRAME_STATE`,
   `NFA_PREFIX_SPILL`, `NFA_FORCED_PREFIX`, and `NFA_PRIMARY_WEIGHT`.

Using a thread-local `Cell` adds zero bytes to the frame enum and
requires no save/restore -- the weight is strictly monotonically
increasing along the parse path and needs no per-frame rollback.

### 4.3 Reset Scope

The accumulator is reset at the *wrapper* function level
(`parse_<cat>`), not per-frame or per `_impl` call.  This means:

- Re-entrant calls (standalone parse functions for ZipMapSep,
  multi-binder, or ident-lookahead rules) see the accumulated weight
  from the outer parse, which is correct: they inherit the confidence
  context of their caller.
- The outermost call always starts from 0.0, ensuring no stale weight
  from a previous parse leaks across invocations.

---

## 5. Weight Scale

The WFST pipeline assigns tropical weights to dispatch actions based
on their ambiguity cost.  These weights flow directly into
`RUNNING_WEIGHT` during accumulation.

| Dispatch Action           | Tropical Weight   | Accumulates |
|---------------------------|-------------------|-------------|
| `Direct`                  | 0.0               | No effect   |
| `Grouping`                | 0.0               | No effect   |
| `CrossCategory` (no BT)   | 0.0               | No effect   |
| `CrossCategory` (with BT) | 0.5               | +0.5        |
| `Cast`                    | 0.5               | +0.5        |
| `Lookahead` (order *k*)   | 1.0 + *k*         | +1.0+       |
| `Variable`                | 2.0               | +2.0        |

**Source:** `wfst.rs:compute_action_weight()`

### 5.1 Interpretation

The running weight at any point in the parse is the sum of all
accumulated dispatch weights along the path from the start of the
current `parse_<cat>` call to the current position:

```
running_weight = SUM_{i=0}^{n} weight(dispatch_i)
```

where *n* is the number of NFA merged-arm dispatches encountered so
far.

- **0.0**: Every dispatch was Direct or Grouping -- fully deterministic.
- **0.5**: One Cast or backtracking CrossCategory dispatch.
- **1.0**: Two Cast dispatches, or one Lookahead.
- **2.0+**: One Variable dispatch, or four Cast dispatches.

### 5.2 Monotonicity

The running weight is monotonically non-decreasing within a single
`parse_<cat>` invocation because all dispatch weights are non-negative
(tropical semiring values in R+ union {+inf}).  This property is important: once
the weight crosses the threshold, it cannot drop back below it.

---

## 6. Interaction with Frame State

### 6.1 Two Orthogonal Dimensions

The existing `FRAME_STATE_<CAT>` thread-local stores a `(u16, u8)` pair
encoding the current trampoline stack depth and the `FrameKind`
discriminant of the top-of-stack frame:

| FrameKind Value | Name         | Example Frame Variant       |
|-----------------|--------------|-----------------------------|
| 0               | Prefix       | `UnaryPrefix_Neg`           |
| 1               | InfixRHS     | `InfixRHS`                  |
| 3               | Collection   | `CollectionElem_Tuple`      |
| 4               | Group        | `GroupClose`                 |
| 5               | Mixfix       | `Mixfix_Ternary_P2`         |
| 6               | Lambda       | `LambdaBody_Abs`            |
| 7               | Dollar       | `Dollar_Apply`              |
| 8               | CastWrap     | `CastWrap_IntToProc`        |
| 9               | Other        | RD segment frames           |

`FRAME_STATE` provides **structural** context: *where* in the grammar's
nesting structure the error occurred.  `RUNNING_WEIGHT` provides
**semantic** context: *how confidently* the parser reached that point.

### 6.2 Combined Recovery Decision Matrix

When both dimensions are available, the recovery engine can make
more nuanced decisions:

```
                      Accumulated Weight
                     Low (< 1.0)     High (>= 1.0)
                  ┌────────────────┬────────────────┐
  Shallow         │ Skip           │ Insert         │
  (depth < 10)    │ (reliable ctx, │ (ambiguous     │
                  │  discard noise)│  path, keep    │
                  │                │  ctx for replay)│
                  ├────────────────┼────────────────┤
  Deep            │ Skip (discount)│ Insert (prefer)│
  (depth >= 1000) │ (reliable deep │ (ambiguous deep│
                  │  nesting, skip │  nesting, must │
                  │  is cheap)     │  preserve ctx) │
                  ├────────────────┼────────────────┤
  Collection/     │ Insert         │ Insert (strong)│
  Group frame     │ (structural    │ (structural +  │
                  │  bracket       │  semantic both │
                  │  recovery)     │  favor insert) │
                  └────────────────┴────────────────┘
```

The frame-kind multipliers from `RecoveryConfig` (Tier 1) continue to
apply on top of the weight-driven strategy preference.  The two
dimensions compose multiplicatively: the frame-kind multiplier adjusts
the *magnitude* of the cost, while the running weight selects the
*direction* (skip vs insert preference).

### 6.3 No Conflict Between Dimensions

The two dimensions cannot produce contradictory recommendations in
the degenerate case because:

1. In Collection and Group frames, insert is already preferred by the
   Tier 1 multipliers (`collection_insert_mult = 0.5`,
   `group_insert_mult = 0.5`).  High accumulated weight reinforces this
   preference -- the two signals are congruent.

2. In shallow deterministic contexts (low weight, low depth), skip is
   preferred by both the Tier 1 depth penalty
   (`shallow_depth_skip_mult = 2.0`, making skip relatively more
   expensive -- but still cheaper than insert at base cost 0.5 vs 2.0)
   and by the low running weight.

3. The only potential tension arises at *deep* nesting with *high*
   weight.  Here Tier 1 discounts skip (`deep_nesting_skip_mult = 0.5`)
   while B2 prefers insert.  The resolution is correct: high weight
   overrides the depth discount because semantic confidence is a
   stronger signal than structural depth when the parse path itself may
   be wrong.

---

## 7. Worked Example

### 7.1 Grammar Fragment (RhoCalc)

```
category Proc {
    rule Output:    Name "!" "(" Proc ")"            // prefix, direct
    rule Input:     "for" "(" Name "<-" Name ")" "{" Proc "}"  // prefix, direct
    rule Par:       Proc "|" Proc                    // infix
    rule Cast:      Int                              // cast (Int -> Proc)
}

category Int {
    rule NumLit:    INTEGER                           // prefix, direct (native)
    rule Add:       Int "+" Int                      // infix
    rule Neg:       "-" Int                          // unary prefix
    rule CastP:     Proc                             // cast (Proc -> Int)
}
```

### 7.2 Input with Error

```
for ( x <- y ) { x ! ( float(int(z)) + | ) }
                                         ^
                                     error: unexpected "|"
```

### 7.3 Parse Trace with Weight Accumulation

```
parse_proc(tokens, pos=0, min_bp=0)
  RUNNING_WEIGHT_PROC ← 0.0                        // reset at wrapper

  Token "for" → Direct dispatch                      // weight 0.0
  RUNNING_WEIGHT_PROC = 0.0 + 0.0 = 0.0

  Token "(" → Direct (structural)
  Token "x" → Variable dispatch in Name              // weight 2.0 in Name category
  Token "<-" → Direct
  Token "y" → Variable dispatch in Name              // weight 2.0 in Name category
  Token ")" → Direct (structural)
  Token "{" → Direct

  // Now inside the body: parse_proc recursively
  // The wrapper resets RUNNING_WEIGHT for the recursive call

  Token "x" → Variable dispatch in Name              // in Name parse
  Token "!" → Direct in Proc (Output prefix)         // weight 0.0
  RUNNING_WEIGHT_PROC = 0.0

  Token "(" → Direct (structural)

  // Inner expression: float(int(z))
  // "float" could be Name or start of cast chain
  Token "float" → Cast dispatch (Proc → Float)       // weight 0.5
  RUNNING_WEIGHT_PROC = 0.0 + 0.5 = 0.5

  Token "(" → Direct (structural)

  Token "int" → Cast dispatch (Float → Int)           // weight 0.5
  RUNNING_WEIGHT_PROC = 0.5 + 0.5 = 1.0

  Token "(" → Direct
  Token "z" → Variable in Name
  Token ")" → Direct
  // int(z) complete, back in Float context

  Token ")" → Direct
  // float(int(z)) complete, back in Proc context

  Token "+" → Infix (Add in Int, requires cast Proc→Int)
  // Cast dispatch weight already accumulated

  Token "|" → ERROR in Int context
  RUNNING_WEIGHT_PROC = 1.0
```

### 7.4 Recovery Decision

```
At error position ("|"):
  FRAME_STATE_PROC  = (depth=4, FrameKind::Group)   // inside "(" ... ")"
  running_weight    = 1.0                            // >= threshold

  Tier 1 (frame-kind):
    Group frame → insert_mult = 0.5 (insert is discounted)

  B2 (accumulated weight):
    running_weight >= 1.0 → ambiguous regime → prefer insert

  Both dimensions agree: INSERT is preferred.

  Recovery selects: InsertToken(")") at cost 2.0 * 0.5 = 1.0
    (closing the group, allowing the parser to continue after ")")

  Compare with skip:
    SkipToSync would skip "|" and ")" → cost = 2 * 0.5 = 1.0
    But skip discards ")" which is a valid structural token.
    Insert preserves context and is preferred under ambiguity.
```

### 7.5 Contrast: Deterministic Path

If the same error occurred on a deterministic path (no casts):

```
x ! ( y + | )
          ^
  running_weight = 0.0    // all Direct dispatches
  Regime: deterministic → prefer skip

  SkipToSync: skip "|" to sync on ")" → cost = 0.5
  InsertToken: insert something before "|" → cost >= 2.0

  Skip wins: the context before "|" is reliable, so discarding the
  erroneous "|" and syncing to ")" is the correct recovery.
```

---

## 8. Data Flow Diagram

```
  parse_<cat> wrapper
  ┌─────────────────────────────────────────────────────────┐
  │  RUNNING_WEIGHT_CAT.set(0.0)          // reset          │
  │                                                         │
  │  parse_<cat>_impl                                       │
  │  ┌───────────────────────────────────────────────────┐  │
  │  │  'drive loop                                      │  │
  │  │  ┌─────────────────────────────────────────────┐  │  │
  │  │  │  Prefix dispatch                            │  │  │
  │  │  │  ┌───────────────────────────────────────┐  │  │  │
  │  │  │  │  NFA merged arms                      │  │  │  │
  │  │  │  │  ┌─────────────────────────────────┐  │  │  │  │
  │  │  │  │  │  Try alternative 1 (weight w1)  │  │  │  │  │
  │  │  │  │  │  Try alternative 2 (weight w2)  │  │  │  │  │
  │  │  │  │  │  ...                            │  │  │  │  │
  │  │  │  │  │  Sort by weight (ascending)     │  │  │  │  │
  │  │  │  │  │  Select best: nfa_weights[0]    │  │  │  │  │
  │  │  │  │  │                                 │  │  │  │  │
  │  │  │  │  │  RUNNING_WEIGHT_CAT +=          │  │  │  │  │
  │  │  │  │  │      nfa_weights[0]       ──────┼──┼──┼──┼──┤
  │  │  │  │  └─────────────────────────────────┘  │  │  │  │
  │  │  │  └───────────────────────────────────────┘  │  │  │
  │  │  │                                             │  │  │  accumulated
  │  │  │  'unwind loop (infix / continuation)        │  │  │  weight
  │  │  └─────────────────────────────────────────────┘  │  │  (f64)
  │  └───────────────────────────────────────────────────┘  │    │
  └─────────────────────────────────────────────────────────┘    │
                                                                 │
  parse_<cat>_own_recovering                                     │
  ┌─────────────────────────────────────────────────────────┐    │
  │  match parse_<cat>_own(tokens, pos, min_bp) {           │    │
  │      Ok(v) => Some(v),                                  │    │
  │      Err(e) => {                                        │    │
  │          let w = RUNNING_WEIGHT_CAT.get()  ◄────────────┼────┘
  │                                                         │
  │          if w < 1.0 { /* deterministic: prefer skip */ }│
  │          else       { /* ambiguous: prefer insert */    }│
  │                                                         │
  │          errors.push(e);                                │
  │          sync_to(tokens, pos, &|t| is_sync_<cat>(t));   │
  │          None                                           │
  │      }                                                  │
  │  }                                                      │
  └─────────────────────────────────────────────────────────┘
```

---

## 9. Threshold Justification

### 9.1 Why 1.0?

The threshold value 1.0 was chosen to correspond to approximately
two ambiguous dispatch decisions:

| Scenario | Running Weight | Regime |
|----------|---------------|--------|
| All Direct/Grouping | 0.0 | Deterministic |
| One Cast | 0.5 | Deterministic |
| One Cast + one CrossCategory(BT) | 1.0 | Ambiguous |
| Two Casts | 1.0 | Ambiguous |
| One Lookahead (order 0) | 1.0 | Ambiguous |
| One Variable | 2.0 | Ambiguous |

Two ambiguous dispatches represent a meaningful branching point in the
parse.  After two such decisions, the probability that the parser is on
the *correct* path has been reduced by the compounding uncertainty of
each branch.

### 9.2 Single-Dispatch Boundary

A single Cast dispatch (weight 0.5) remains in the deterministic regime.
This is intentional: cast chains like `int(x)` are common and usually
unambiguous in practice.  A single cast does not significantly reduce
parse confidence because the WFST pre-orders alternatives by weight, and
the 0.5 weight on Cast is a *disambiguation penalty*, not a confidence
measure.  Only when two or more such penalties accumulate does the
aggregate uncertainty warrant a strategy change.

### 9.3 Variable Dispatch

A single `Variable` dispatch (weight 2.0) immediately exceeds the
threshold.  This is correct: Variable is the fallback when no
specific token matches any Direct, Cast, or CrossCategory arm.  It
represents maximal ambiguity -- the parser is guessing -- and insert
is the appropriate recovery strategy to preserve whatever context
exists.

### 9.4 Tuning

The threshold 1.0 is a compile-time default.  Future work could expose
it as a field in `RecoveryConfig` (analogous to `deep_nesting_threshold`
and `shallow_depth_threshold`) to allow grammar authors to tune the
sensitivity of the adaptive recovery mechanism.  Grammars with many
casts (e.g., multi-sorted algebras) might raise the threshold; grammars
with few ambiguities might lower it.

---

## 10. RecoveryConfig Integration

### 10.1 Current Status

The adaptive recovery reads `RUNNING_WEIGHT` but does not yet modulate
the `RecoveryConfig` fields dynamically.  The current implementation
uses the weight to *select* between skip and insert at the top level
of the recovering function.  The per-strategy costs from
`RecoveryConfig` are applied afterward by the existing Tier 1/2/3
multiplier chain.

### 10.2 Potential Extension Fields

A future extension could add the following fields to `RecoveryConfig`:

| Field | Type | Default | Semantics |
|-------|------|---------|-----------|
| `adaptive_weight_threshold` | `f64` | 1.0 | Running weight above which insert is preferred |
| `deterministic_skip_discount` | `f64` | 0.75 | Skip cost multiplier when below threshold |
| `ambiguous_insert_discount` | `f64` | 0.5 | Insert cost multiplier when above threshold |

These fields would allow the threshold and the cost modulation to be
tuned per grammar, trained via the SGD loop in `train_recovery_weights()`,
or set explicitly by the grammar author.

### 10.3 Interaction with Trained Weights

The `apply_trained_weights()` method on `RecoveryConfig` currently
accepts five base cost keys.  The potential extension fields would
require additional keys (`adaptive_weight_threshold`,
`deterministic_skip_discount`, `ambiguous_insert_discount`) in the
training vocabulary.  The training loop would need paired error corpora
with known-ambiguous and known-deterministic paths to learn the
optimal threshold and discount values.

---

## 11. Source Reference

| Component | Location |
|-----------|----------|
| Thread-local declarations | `trampoline.rs:write_trampolined_parser()` lines 1143--1173 |
| Weight reset in wrapper | `trampoline.rs:write_trampolined_parser()` line 1200 |
| Accumulation in NFA dispatch | `trampoline.rs:write_nfa_merged_arms()` line 395 |
| Accessor function | `trampoline.rs:write_trampolined_parser()` lines 1175--1184 |
| Recovery reading | `trampoline.rs:write_recovering_function()` lines 3019--3039 |
| Dispatch weight assignment | `wfst.rs:compute_action_weight()` lines 567--579 |
| RecoveryConfig struct | `recovery.rs:RecoveryConfig` lines 108--166 |
| Frame state thread-local | `trampoline.rs:write_trampolined_parser()` lines 1083--1095 |
| Frame-kind classifier | `trampoline.rs:write_trampolined_parser()` lines 1097--1141 |
| Frame state update in drive loop | `trampoline.rs:write_trampoline_body()` lines 1257--1270 |
