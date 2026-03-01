# Layer 2.5: NFA Intra-Category Disambiguation

Layer 2.5 sits between parse prediction (Layer 2) and operator precedence
(Layer 3) in PraTTaIL's disambiguation model. It resolves **intra-category**
parse ambiguity — situations where multiple grammar rules within the same
category share the same dispatch token and cannot be distinguished by 2-token
lookahead.

Where Layer 2 handles inter-rule dispatch ("which rule for this token?") and
Layer 4 handles inter-category dispatch ("which category for this token?"),
Layer 2.5 handles the case where Layer 2's dispatch table maps a single token
to **multiple rules within one category**, all of which are structurally valid
parses.

**Source files:**
- `prattail/src/trampoline.rs` — `categories_needing_nfa_spillover()`,
  `group_rd_by_dispatch_token()`, `write_nfa_merged_prefix_arm()`,
  `write_nfa_inline_constructor()`
- `prattail/src/pipeline.rs` — NFA spillover detection, CountingWeight
  ambiguity warnings
- `prattail/src/wfst.rs` — `PredictionWfst::nfa_alternative_order()`
- `macros/src/gen/runtime/language.rs` — drain loop, `AMBIGUOUS_WEIGHTS`,
  weight-aware `from_alternatives()`

**Cross-references:**
- [02-parse-prediction.md](02-parse-prediction.md) — Layer 2 dispatch tables
  and FIRST set analysis; §7.1 superseded by this document's §4.2
- [06-layer-interactions.md](06-layer-interactions.md) — End-to-end traces
  including Layer 2.5
- [07-semantic-disambiguation.md](07-semantic-disambiguation.md) — Layer 6
  semantic resolution using the results Layer 2.5 produces
- [../../architecture/wfst/pipeline-integration.md](../../architecture/wfst/pipeline-integration.md)
  — Pipeline step 5g (NFA spillover detection)
- [../../architecture/generated-code-anatomy.md](../../architecture/generated-code-anatomy.md)
  — Part 19 (NFA merged prefix arm codegen)

---

## Table of Contents

1. [The Intra-Category Ambiguity Problem](#1-the-intra-category-ambiguity-problem)
2. [Three-Phase Architecture Overview](#2-three-phase-architecture-overview)
3. [Phase 1: NFA Try-All and Forced-Prefix Replay](#3-phase-1-nfa-try-all-and-forced-prefix-replay)
4. [Phase 2: Beam Pruning and Ambiguity Warnings](#4-phase-2-beam-pruning-and-ambiguity-warnings)
5. [Phase 3: Weight-Annotated Spillover and Weight-Aware from_alternatives](#5-phase-3-weight-annotated-spillover-and-weight-aware-from_alternatives)
6. [Zero-Overhead Design](#6-zero-overhead-design)
7. [Interaction with Disambiguation Layers](#7-interaction-with-disambiguation-layers)
8. [Source Map](#8-source-map)

---

## 1. The Intra-Category Ambiguity Problem

Consider the Calculator language's `Float` category. It contains four rules
that all begin with `Token::KwFloat` (the keyword `float`):

```
Float category rules starting with "float(":
  FloatId    . a:Float         |- "float" "(" a ")"           : Float
  IntToFloat . a:Int           |- "float" "(" a ")"           : Float
  BoolToFloat . a:Bool         |- "float" "(" a ")"           : Float
  StrToFloat . a:Str           |- "float" "(" a ")"           : Float
```

All four rules share the same first terminal (`"float"`), the same second
terminal (`"("`), and the same closing delimiter (`")"`). They differ only in
the **type of the inner expression** — and that type is determined by parsing,
not by looking at the next token. Layer 2's dispatch table cannot emit a
`Direct` action because the FIRST sets of `Int`, `Float`, `Bool`, and `Str`
all contain `Ident` (any variable name could belong to any type):

```
Layer 2 dispatch for Float, token KwFloat:

  Token        Candidate Rules              Decision
  ─────────────────────────────────────────────────────
  KwFloat  →   FloatId, IntToFloat,         AMBIGUOUS
               BoolToFloat, StrToFloat       (4-way)
```

Two-token lookahead does not help either: the second token is always `LParen`
regardless of which rule will succeed.

Before Layer 2.5, this ambiguity triggered a compile-time `AmbiguousPrefix`
warning but was not resolved — the parser would arbitrarily try one rule and
fail on the others. Layer 2.5 introduces a structured mechanism to try **all**
candidate rules, collect their results, and defer resolution to semantic
disambiguation (Layer 6).

---

## 2. Three-Phase Architecture Overview

Layer 2.5 operates in three phases, two at compile time and one spanning both
compile time and runtime:

```
  ┌─────────────────────────────────────────────────────────────────────┐
  │  COMPILE TIME                                                       │
  │                                                                     │
  │  ┌───────────────────────────────────────────────────────────────┐  │
  │  │  Phase 1: NFA Try-All + Forced-Prefix Replay                 │  │
  │  │                                                               │  │
  │  │  Detect NFA-ambiguous categories:                             │  │
  │  │    categories_needing_nfa_spillover()                         │  │
  │  │    group_rd_by_dispatch_token()                               │  │
  │  │                                                               │  │
  │  │  Order alternatives by WFST weight:                           │  │
  │  │    nfa_alternative_order() → sorted by tropical weight        │  │
  │  │                                                               │  │
  │  │  Generate merged prefix arm:                                  │  │
  │  │    write_nfa_merged_prefix_arm()                              │  │
  │  │    → save/restore loop, result selection, spillover           │  │
  │  │                                                               │  │
  │  │  Generate thread-local declarations:                          │  │
  │  │    NFA_PREFIX_SPILL_CAT, NFA_FORCED_PREFIX_CAT,              │  │
  │  │    NFA_PRIMARY_WEIGHT_CAT                                    │  │
  │  │                                                               │  │
  │  │  Generate forced-prefix check:                                │  │
  │  │    prefix block entry → take forced → skip NFA → infix loop  │  │
  │  └───────────────────────────────────────────────────────────────┘  │
  │                                                                     │
  │  ┌───────────────────────────────────────────────────────────────┐  │
  │  │  Phase 2: Beam Pruning + Ambiguity Warnings                  │  │
  │  │                                                               │  │
  │  │  Compile-time beam pruning:                                   │  │
  │  │    Filter alternatives where weight > best + beam_width       │  │
  │  │    Pruned alternatives never appear in generated code         │  │
  │  │                                                               │  │
  │  │  CountingWeight ambiguity diagnostics:                        │  │
  │  │    Equal-weight detection → deferred resolution warning       │  │
  │  │    Supersedes old AmbiguousPrefix warning                     │  │
  │  └───────────────────────────────────────────────────────────────┘  │
  │                                                                     │
  └─────────────────────────────────────────────────────────────────────┘

  ┌─────────────────────────────────────────────────────────────────────┐
  │  RUNTIME (generated code)                                           │
  │                                                                     │
  │  ┌───────────────────────────────────────────────────────────────┐  │
  │  │  Phase 3: Weight-Annotated Spillover + Weight-Aware          │  │
  │  │           from_alternatives                                  │  │
  │  │                                                               │  │
  │  │  NFA merged arm:                                              │  │
  │  │    Try all alternatives, collect (result, position, weight)   │  │
  │  │    Best result → caller; N-1 → NFA_PREFIX_SPILL              │  │
  │  │                                                               │  │
  │  │  parse_preserving_vars drain loop:                            │  │
  │  │    Primary parse → record NFA_PRIMARY_WEIGHT                 │  │
  │  │    Drain NFA_PREFIX_SPILL → forced-prefix replay             │  │
  │  │    Each replay: set NFA_FORCED_PREFIX → Cat::parse(input)    │  │
  │  │    Collect successes + weights                                │  │
  │  │                                                               │  │
  │  │  Weight-aware from_alternatives:                              │  │
  │  │    AMBIGUOUS_WEIGHTS thread-local carries weights             │  │
  │  │    Multiple accepting → min-weight (tropical) wins            │  │
  │  └───────────────────────────────────────────────────────────────┘  │
  │                                                                     │
  └─────────────────────────────────────────────────────────────────────┘
```

---

## 3. Phase 1: NFA Try-All and Forced-Prefix Replay

### 3.1 Compile-Time Detection

The pipeline detects which categories have NFA-ambiguous prefix groups using
two functions in `trampoline.rs`:

**`group_rd_by_dispatch_token()`** (lines 77–116) groups all RD rules for a
category by their first terminal token:

```
group_rd_by_dispatch_token(rd_rules, "Float"):

  KwFloat → [FloatId, IntToFloat, BoolToFloat, StrToFloat]   ← 4 rules!
  KwInt   → [FloatToInt]                                      ← 1 rule
  KwBool  → [FloatToBool]                                     ← 1 rule
  KwStr   → [FloatToStr]                                      ← 1 rule
  ...
```

Rules are filtered to exclude:
- Simple collections (have their own specialized handler)
- Unary prefix operators (have `prefix_bp`, handled by Pratt loop)
- Rules starting with a nonterminal or ident capture (handled by variable
  fallback or cross-category dispatch)

A group with more than one rule indicates NFA ambiguity.

**`categories_needing_nfa_spillover()`** (lines 136–151) iterates all
categories and checks whether any token group has `len() > 1`:

```
categories_needing_nfa_spillover(rd_rules, ["Int","Float","Bool","Str"]):

  Int:   group_rd_by_dispatch_token → no multi-rule groups   → skip
  Float: group_rd_by_dispatch_token → KwFloat has 4 rules   → INSERT "Float"
  Bool:  group_rd_by_dispatch_token → no multi-rule groups   → skip
  Str:   group_rd_by_dispatch_token → no multi-rule groups   → skip

  Result: {"Float"}
```

The result is stored in `TrampolineConfig.needs_nfa_spillover` (set in
`pipeline.rs`, line 910), which controls whether NFA spillover codegen
is emitted for that category.

### 3.2 WFST Weight Ordering

When a WFST is available for a category, alternatives are sorted by tropical
weight (lowest = most likely). This is done by `nfa_alternative_order()` in
`wfst.rs` (lines 198–218):

```
nfa_alternative_order("KwFloat", ["FloatId","IntToFloat","BoolToFloat","StrToFloat"]):

  Predict actions for KwFloat:
    FloatId    → weight 0.50   (identity cast, highest priority)
    IntToFloat → weight 1.00   (conversion rule)
    BoolToFloat → weight 1.50  (conversion rule, lower specificity)
    StrToFloat → weight 2.00   (conversion rule, lowest specificity)

  Sort by weight ascending:
    [(0, 0.50), (1, 1.00), (2, 1.50), (3, 2.00)]
```

The return type `Vec<(usize, TropicalWeight)>` gives the original index into
the rule list paired with the weight. Rules not found in the WFST receive a
default weight of `0.5` (cast-level priority).

This ordering determines:
1. The order in which alternatives are tried (best first)
2. Which alternative is returned as the primary result (index 0 = best)
3. The weight annotations carried through spillover

### 3.3 Generated NFA Merged Prefix Arm

For each NFA-ambiguous token group, `write_nfa_merged_prefix_arm()` (lines
162–361) generates a `match` arm that tries all alternatives via save/restore:

```rust
// Generated code for Float prefix, token KwFloat (annotated pseudocode)
Token::KwFloat => {
    // 1. Checkpoint: save current position
    let nfa_saved = *pos;

    // 2. Collectors
    let mut nfa_results: Vec<Float> = Vec::new();
    let mut nfa_positions: Vec<usize> = Vec::new();
    let mut nfa_weights: Vec<f64> = Vec::new();
    let mut nfa_first_err: Option<ParseError> = None;

    // 3. Try FloatId (weight 0.50 — best, tried first)
    *pos = nfa_saved;
    match (|| -> Result<Float, ParseError> {
        // ... parse "float" "(" Float ")" → FloatId(a)
        Ok(Float::FloatId(Box::new(a)))
    })() {
        Ok(v) => {
            nfa_results.push(v);
            nfa_positions.push(*pos);
            nfa_weights.push(0.50);
        }
        Err(e) => { if nfa_first_err.is_none() { nfa_first_err = Some(e); } }
    }

    // 4. Try IntToFloat (weight 1.00)
    *pos = nfa_saved;
    match (|| -> Result<Float, ParseError> {
        // ... parse "float" "(" Int ")" → IntToFloat(a)
        Ok(Float::IntToFloat(Box::new(a)))
    })() {
        Ok(v) => {
            nfa_results.push(v);
            nfa_positions.push(*pos);
            nfa_weights.push(1.00);
        }
        Err(e) => { if nfa_first_err.is_none() { nfa_first_err = Some(e); } }
    }

    // ... (same pattern for BoolToFloat at 1.50 and StrToFloat at 2.00)

    // 5. Result selection
    match nfa_results.len() {
        0 => {
            // All alternatives failed — return first error
            return Err(nfa_first_err.expect("at least one error"));
        }
        _ => {
            // Best result (index 0, lowest weight) returned to caller
            *pos = nfa_positions[0];
            let best = nfa_results.remove(0);
            let _best_weight = nfa_weights.remove(0);

            // Spill N-1 remaining alternatives to thread-local
            // (only those that consumed the same number of tokens)
            let mut spill = Vec::new();
            for i in 0..nfa_results.len() {
                if nfa_positions[i] == nfa_positions[0] {
                    spill.push((
                        nfa_results.remove(0),
                        nfa_positions[i],
                        nfa_weights[i],
                    ));
                }
            }
            NFA_PREFIX_SPILL_FLOAT.with(|cell| cell.set(spill));
            NFA_PRIMARY_WEIGHT_FLOAT.with(|cell| cell.set(_best_weight));

            break 'prefix best;
        }
    }
}
```

Each alternative is wrapped in a closure `(|| -> Result<Cat, ParseError> { ... })()`
so that early returns from `expect_token` and recursive `parse_Cat` calls are
captured as `Err` without aborting the outer NFA loop. The closure uses
`Ok(Cat::Label(...))` rather than `break 'prefix Cat::Label(...)` because it
executes inside the closure scope.

### 3.4 Thread-Local Declarations

Three thread-locals are emitted per category (`trampoline.rs`, lines
1082–1103). They are emitted for **all** categories (not just NFA-ambiguous
ones) so that `parse_preserving_vars` can unconditionally drain them:

```rust
thread_local! {
    /// Spillover buffer: N-1 prefix alternatives from NFA merged arms.
    /// Each entry is (prefix_value, end_position, tropical_weight).
    static NFA_PREFIX_SPILL_FLOAT: std::cell::Cell<Vec<(Float, usize, f64)>> =
        std::cell::Cell::new(Vec::new());

    /// Forced prefix override: when replay sets this to Some(...),
    /// the parser skips NFA try-all and uses this value directly.
    static NFA_FORCED_PREFIX_FLOAT: std::cell::Cell<Option<(Float, usize, f64)>> =
        std::cell::Cell::new(None);

    /// Weight of the primary (returned) NFA result.
    /// Default 0.5 when no NFA ambiguity occurred.
    static NFA_PRIMARY_WEIGHT_FLOAT: std::cell::Cell<f64> =
        std::cell::Cell::new(0.5);
}
```

All three use `Cell` (not `RefCell`) because the trampoline's standalone
functions may cause re-entrancy. `Cell::take()` and `Cell::set()` are safe
for re-entrant access patterns — `Cell::take()` on an empty `Vec` is
essentially a pointer swap and `Cell::set()` of a default `f64` is a register
write.

### 3.5 The `parse_preserving_vars` Drain and Replay Loop

The NFA spillover drain occurs in the macro-generated `parse_preserving_vars`
function (`macros/src/gen/runtime/language.rs`, lines 1116–1161). This
function already runs each category parser as part of Layer 6's NFA-style
multi-category parse. The drain extends this with intra-category alternatives:

```
parse_preserving_vars(input):
  successes = []
  success_weights = []
  first_err = None

  for each category Cat in parse_order:
    match Cat::parse(input):
      Ok(term) →
        successes.push(TermInner::Cat(term))

        // Record primary result's WFST weight
        w = NFA_PRIMARY_WEIGHT_CAT.take()    // read and reset to 0.5
        success_weights.push(w)

        // Drain NFA prefix spillover
        spilled = NFA_PREFIX_SPILL_CAT.take()    // take and replace with empty Vec
        for (alt_prefix, alt_pos, alt_weight) in spilled:
          // Set forced-prefix override for replay
          NFA_FORCED_PREFIX_CAT.set(Some((alt_prefix, alt_pos, alt_weight)))

          // Re-parse: the parser sees the forced prefix, skips NFA try-all,
          // and runs the infix loop with the forced prefix value
          match Cat::parse(input):
            Ok(alt_term) →
              successes.push(TermInner::Cat(alt_term))
              success_weights.push(alt_weight)
            Err(_) → ()    // silently discard failed replay

          // Clear any nested spillover from forced-prefix replay
          NFA_PREFIX_SPILL_CAT.take()

      Err(e) →
        // Clear spillover on error to prevent leaking across categories
        NFA_PREFIX_SPILL_CAT.take()
        if first_err is None: first_err = Some(e)

  // Set weights for from_alternatives tiebreaking
  AMBIGUOUS_WEIGHTS.set(success_weights)
  match successes.len():
    0 → Err(first_err)
    1 → Ok(Term(successes[0]))
    _ → Ok(Term(from_alternatives(successes)))
```

The replay mechanism works as follows:

1. The primary parse of `Cat::parse(input)` runs normally. Inside the
   trampoline, the NFA merged arm tries all alternatives and returns the best
   one. N-1 alternatives are spilled to `NFA_PREFIX_SPILL_CAT`.

2. After the primary parse succeeds, `parse_preserving_vars` drains the
   spillover into a local `spilled` vec.

3. For each spilled alternative `(alt_prefix, alt_pos, alt_weight)`:
   - Sets `NFA_FORCED_PREFIX_CAT` to `Some((alt_prefix, alt_pos, alt_weight))`
   - Calls `Cat::parse(input)` again
   - The parser's forced-prefix check (§3.6) intercepts this, skips the NFA
     merged arm entirely, and uses `alt_prefix` as the prefix result
   - The infix loop then runs normally, giving the alternative its correct
     infix context (e.g., `float(x) + 1.0` continues with `+` binding)
   - Clears any nested spillover to prevent cascading

4. All successes and their weights are collected for `from_alternatives()`.

### 3.6 Forced-Prefix Check

At the very start of each category's `'prefix` block, the generated code
checks for a forced prefix override (`trampoline.rs`, lines 1261–1277):

```rust
// Generated at the top of parse_Float prefix block
{
    let forced = NFA_FORCED_PREFIX_FLOAT.with(|cell| cell.take());
    if let Some((forced_val, forced_pos, _forced_weight)) = forced {
        *pos = forced_pos;
        break 'prefix forced_val;
    }
}
// ... normal prefix match follows only if no forced prefix was set
```

This check is always emitted (even for non-NFA-ambiguous categories) to
ensure the forced-prefix replay works for any category that might receive a
replay from `parse_preserving_vars`. The cost when no forced prefix is set
is a single `Cell::take()` on `None` — effectively zero.

### 3.7 End-to-End Trace: `float(x) + 1.0`

This trace follows a complete execution of NFA disambiguation for the
Calculator's Float category, where `x` is an unbound variable.

```
Input: "float(x) + 1.0"
Tokens: [KwFloat, LParen, Ident("x"), RParen, Plus, Float(1.0), Eof]

═══════════════════════════════════════════════════════════════════════
Layer 2.5: NFA Merged Prefix Arm (Float, token KwFloat)
═══════════════════════════════════════════════════════════════════════

  nfa_saved = 0

  Try FloatId (weight 0.50):
    *pos = 0 → parse "float" "(" Float ")" →
    parse_Float(inner, pos=2): Ident("x") → FloatVar("x"). pos=3.
    expect ")": pos=4.
    → Ok(FloatId(FloatVar("x"))). pos=4, weight=0.50.

  Try IntToFloat (weight 1.00):
    *pos = 0 → parse "float" "(" Int ")" →
    parse_Int(inner, pos=2): Ident("x") → IntVar("x"). pos=3.
    expect ")": pos=4.
    → Ok(IntToFloat(IntVar("x"))). pos=4, weight=1.00.

  Try BoolToFloat (weight 1.50):
    *pos = 0 → parse "float" "(" Bool ")" →
    parse_Bool(inner, pos=2): Ident("x") → BoolVar("x"). pos=3.
    expect ")": pos=4.
    → Ok(BoolToFloat(BoolVar("x"))). pos=4, weight=1.50.

  Try StrToFloat (weight 2.00):
    *pos = 0 → parse "float" "(" Str ")" →
    parse_Str(inner, pos=2): Ident("x") → StrVar("x"). pos=3.
    expect ")": pos=4.
    → Ok(StrToFloat(StrVar("x"))). pos=4, weight=2.00.

  Result: 4 successes. Best = FloatId(FloatVar("x")) at weight 0.50.
  Spill: [(IntToFloat(IntVar("x")), 4, 1.00),
          (BoolToFloat(BoolVar("x")), 4, 1.50),
          (StrToFloat(StrVar("x")), 4, 2.00)]
  → NFA_PREFIX_SPILL_FLOAT.set(spill)
  → NFA_PRIMARY_WEIGHT_FLOAT.set(0.50)

  break 'prefix FloatId(FloatVar("x"))

═══════════════════════════════════════════════════════════════════════
Layer 3: Infix Loop (Float)
═══════════════════════════════════════════════════════════════════════

  lhs = FloatId(FloatVar("x")), pos = 4
  Token: Plus. infix_bp_Float(Plus) = Some((2, 3)).
  left_bp=2 ≥ min_bp=0 → Plus binds.
  Consume Plus. pos = 5.
  parse_Float(tokens, pos=5, min_bp=3):
    prefix: Float(1.0) → FloatLit(1.0). pos = 6.
    infix loop: Eof → break.
  rhs = FloatLit(1.0).
  lhs = FloatAdd(FloatId(FloatVar("x")), FloatLit(1.0)).

  Float::parse returns Ok(FloatAdd(FloatId(FloatVar("x")), FloatLit(1.0))).

═══════════════════════════════════════════════════════════════════════
Layer 6: parse_preserving_vars drain
═══════════════════════════════════════════════════════════════════════

  Primary success: Float(FloatAdd(FloatId(FloatVar("x")), FloatLit(1.0)))
  success_weights[0] = 0.50

  Drain NFA_PREFIX_SPILL_FLOAT:
    spilled = [(IntToFloat(IntVar("x")), 4, 1.00),
               (BoolToFloat(BoolVar("x")), 4, 1.50),
               (StrToFloat(StrVar("x")), 4, 2.00)]

  Replay 1: IntToFloat(IntVar("x")), weight 1.00
    NFA_FORCED_PREFIX_FLOAT.set(Some((IntToFloat(IntVar("x")), 4, 1.00)))
    Float::parse("float(x) + 1.0"):
      Forced prefix: take → Some((IntToFloat(IntVar("x")), 4, _)).
      *pos = 4. break 'prefix IntToFloat(IntVar("x")).
      Infix loop: Plus binds → FloatAdd(IntToFloat(IntVar("x")), FloatLit(1.0)).
    → Ok. successes.push, success_weights.push(1.00).

  Replay 2: BoolToFloat(BoolVar("x")), weight 1.50
    (same pattern → FloatAdd(BoolToFloat(BoolVar("x")), FloatLit(1.0)))

  Replay 3: StrToFloat(StrVar("x")), weight 2.00
    (same pattern → FloatAdd(StrToFloat(StrVar("x")), FloatLit(1.0)))

  successes = [
    Float(FloatAdd(FloatId(FVar("x")),    FloatLit(1.0))),   weight 0.50
    Float(FloatAdd(IntToFloat(IVar("x")), FloatLit(1.0))),   weight 1.00
    Float(FloatAdd(BoolToFloat(BVar("x")),FloatLit(1.0))),   weight 1.50
    Float(FloatAdd(StrToFloat(SVar("x")), FloatLit(1.0))),   weight 2.00
  ]

═══════════════════════════════════════════════════════════════════════
Layer 6: from_alternatives with weights
═══════════════════════════════════════════════════════════════════════

  4 alternatives, 0 ground (all contain variables) → Ambiguous([...])
  Later: substitute_env resolves based on what "x" is bound to.
    e.g., x=42 (Int env) → IntToFloat progresses → Float wins.
```

The critical design point is that each replay runs the **complete** parser
(prefix + infix loop), not just the prefix. This means the alternative
`IntToFloat(IntVar("x"))` gets the correct infix context: `+ 1.0` binds as
a Float addition, producing `FloatAdd(IntToFloat(IntVar("x")), FloatLit(1.0))`.
Without this replay, only the prefix would be captured, and the infix `+ 1.0`
would be lost.

---

## 4. Phase 2: Beam Pruning and Ambiguity Warnings

### 4.1 Compile-Time Beam Pruning

When a grammar configures a beam width (via `beam_width: <value>` in the
language spec), alternatives whose WFST weight exceeds `best_weight + beam_width`
are pruned at compile time. Pruned alternatives never appear in the generated
code — they are simply not emitted in the NFA merged arm's try loop.

The pruning occurs in `write_nfa_merged_prefix_arm()` (lines 222–242):

```
ordered_inlineable = nfa_alternative_order(variant, rule_labels)
beam = wfst.beam_width()
best_weight = ordered[0].weight

filtered = ordered.filter(|(_, w)|
    match (beam, best_weight):
      (Some(beam_w), Some(best_w)) → w ≤ best_w + beam_w
      _ → true    // no beam → keep all
)
```

For example, with `beam_width: 1.0` and the Float alternatives:

```
FloatId:     0.50   ← best
IntToFloat:  1.00   ← 1.00 ≤ 0.50 + 1.0 = 1.50 ✓ keep
BoolToFloat: 1.50   ← 1.50 ≤ 1.50 ✓ keep
StrToFloat:  2.00   ← 2.00 > 1.50 ✗ PRUNED
```

`StrToFloat` is never tried at runtime, reducing code size and try-loop
iterations. This is a **compile-time** decision — no runtime beam check
is needed in the generated NFA merged arm.

### 4.2 CountingWeight Ambiguity Warnings

The pipeline emits structured diagnostics for NFA-ambiguous token groups
using CountingWeight analysis (`pipeline.rs`, lines 800–840):

```
warning: ambiguous prefix dispatch for token "KwFloat" in category Float:
         rules ["FloatId", "IntToFloat", "BoolToFloat", "StrToFloat"] all match
  → all 4 alternatives have equal weight (0.5);
    resolution deferred to semantic disambiguation
```

The equal-weight detection identifies cases where the WFST cannot differentiate
alternatives (all weights are within ε = 10⁻¹² of each other), indicating
that resolution must be deferred entirely to Layer 6.

### 4.3 Old vs New Warnings

| Before (Layer 2)                       | After (Layer 2.5)                                              |
|----------------------------------------|----------------------------------------------------------------|
| `AmbiguousPrefix` in `prediction.rs`   | Suppressed (superseded)                                        |
| Generic "rules X, Y share token T"     | Specific "NFA-ambiguous, N alternatives, weights [w₁, ..., wₙ]" |
| No resolution mechanism                | Full NFA try-all + forced-prefix replay                        |
| No weight information                  | Weight ordering from WFST prediction                           |

The old `AmbiguousPrefix` warning from `prediction.rs` (`detect_ambiguous_prefix()`,
lines 861–900) is suppressed for rules that are handled by NFA merged arms.
Only truly unresolvable ambiguities (if any remained after NFA handling) would
still trigger the old warning. See
[02-parse-prediction.md](02-parse-prediction.md) §7.1 for the supersession note.

---

## 5. Phase 3: Weight-Annotated Spillover and Weight-Aware `from_alternatives`

### 5.1 Weight Carriage in Spillover Tuples

Each spilled alternative carries three values as a tuple `(Cat, usize, f64)`:

| Field   | Type    | Purpose                                                      |
|---------|---------|--------------------------------------------------------------|
| `.0`    | `Cat`   | The parsed prefix value (e.g., `IntToFloat(IntVar("x"))`)   |
| `.1`    | `usize` | The `pos` after parsing this alternative (end position)      |
| `.2`    | `f64`   | The WFST tropical weight (lower = more likely)               |

The position field is essential for correct replay: when the forced-prefix
check fires (§3.6), it sets `*pos = forced_pos` so the infix loop starts at
the correct token. Without this, all alternatives would share the primary
result's end position, which could be wrong if different alternatives consume
different numbers of prefix tokens.

### 5.2 The `AMBIGUOUS_WEIGHTS` Thread-Local

A single language-level thread-local carries weights from `parse_preserving_vars`
to `from_alternatives()` (`macros/src/gen/runtime/language.rs`, lines 1529–1535):

```rust
thread_local! {
    /// WFST weights parallel to the `successes` vec.
    /// Set before `from_alternatives` so it can use weights as tiebreaker.
    static AMBIGUOUS_WEIGHTS: std::cell::Cell<Vec<f64>> =
        std::cell::Cell::new(Vec::new());
}
```

This thread-local is set immediately before calling `from_alternatives()`
in `parse_preserving_vars`:

```rust
AMBIGUOUS_WEIGHTS.with(|cell| cell.set(success_weights));
Ok(Term(TermInner::from_alternatives(successes)))
```

### 5.3 Weight-Aware `from_alternatives`

When `from_alternatives()` finds multiple accepting (ground) alternatives,
it uses the WFST weights as a tiebreaker to select the most likely one
(`language.rs`, lines 302–321):

```
from_alternatives(alts):
  flat = flatten(alts)         // unwrap nested Ambiguous
  n_alts = flat.len()

  if n_alts == 0: panic
  if n_alts == 1: return flat[0]

  accepting = flat.filter(is_accepting)    // ground terms only

  match accepting.len():
    0 → Ambiguous(flat)                    // no ground → defer to substitution
    1 → accepting[0]                       // exactly one ground → unambiguous
    n if n > 1 →
      // Multiple ground alternatives: WFST weight tiebreaker
      weights = AMBIGUOUS_WEIGHTS.take()
      if weights.len() == n_alts AND flat.len() == n_alts:
        // Parallel length invariant holds: select min-weight accepting
        best_idx = accepting
          .min_by(|(i, _), (j, _)| weights[i].partial_cmp(&weights[j]))
          .index
        return flat[best_idx]
      else:
        // Length mismatch (nested Ambiguous changed flat.len) → first accepting
        return accepting[0]
```

### 5.4 Parallel Length Invariant

The weight-aware path requires that `weights.len() == n_alts` and
`flat.len() == n_alts` (i.e., no nested `Ambiguous` changed the flat count).
When this invariant holds, each `weights[i]` corresponds to `flat[i]` and the
min-weight lookup is valid. When it does not hold (because flattening changed
the count), the fallback is to return the first accepting alternative —
which is the first-declared category per the declaration-order invariant
(see [07-semantic-disambiguation.md](07-semantic-disambiguation.md) §6).

---

## 6. Zero-Overhead Design

Layer 2.5 is designed to have zero overhead when it is not triggered:

| Scenario           | Cost                                              |
|--------------------|---------------------------------------------------|
| **Unambiguous**    | `Cell::take()` on `None` / empty `Vec` (ptr swap) |
| **All-fail**       | Single error return, no spillover                 |
| **Ambiguous (1)**  | NFA merged arm: N try-restore + 1 spillover push  |
| **Ambiguous (N)**  | Spillover: N-1 full re-parses via forced prefix   |

The thread-local declarations (`NFA_PREFIX_SPILL`, `NFA_FORCED_PREFIX`,
`NFA_PRIMARY_WEIGHT`) are emitted for all categories but have zero cost when
not used:

- `Cell::take()` on an empty `Vec` is a pointer swap (set `Vec::new()`,
  return the empty `Vec`)
- `Cell::take()` on `None` is a register-width operation
- `Cell::get()` on the default `f64` (0.5) is a register read

When only one NFA alternative succeeds (`nfa_results.len() == 1`), no
spillover is pushed — the successful result is returned directly without
writing to any thread-local.

---

## 7. Interaction with Disambiguation Layers

Layer 2.5 sits between Layer 2 (parse prediction) and Layer 3 (operator
precedence), feeding results into Layer 6 (semantic disambiguation):

```
  ┌───────────────────────────────────────────────────────────────────┐
  │                         SOURCE TEXT                                │
  └────────────────────────────┬──────────────────────────────────────┘
                               │
  ┌────────────────────────────▼──────────────────────────────────────┐
  │  LAYER 1: LEXICAL DISAMBIGUATION                                  │
  │  DFA + maximal munch + priority                                   │
  └────────────────────────────┬──────────────────────────────────────┘
                               │
  ┌────────────────────────────▼──────────────────────────────────────┐
  │  LAYER 2: PARSE PREDICTION                                        │
  │  FIRST sets + dispatch tables + lookahead                         │
  │  → Identifies NFA-ambiguous token groups (cannot resolve)         │
  └────────────────────────────┬──────────────────────────────────────┘
                               │
  ┌────────────────────────────▼──────────────────────────────────────┐
  │  LAYER 2.5: NFA INTRA-CATEGORY DISAMBIGUATION                    │
  │  NFA try-all + forced-prefix replay + weight ordering             │
  │  → Tries all alternatives, collects results, spills to Layer 6   │
  └────────────────────────────┬──────────────────────────────────────┘
                               │
  ┌────────────────────────────▼──────────────────────────────────────┐
  │  LAYER 3: OPERATOR PRECEDENCE                                     │
  │  Binding power pairs + Pratt loop                                 │
  │  → Runs on each alternative independently (during NFA try-all     │
  │    and during forced-prefix replay)                               │
  └────────────────────────────┬──────────────────────────────────────┘
                               │
  ┌────────────────────────────▼──────────────────────────────────────┐
  │  LAYER 4: CROSS-CATEGORY RESOLUTION                               │
  │  FIRST set partition + backtracking dispatch                      │
  └────────────────────────────┬──────────────────────────────────────┘
                               │
  ┌────────────────────────────▼──────────────────────────────────────┐
  │  LAYER 5: ERROR RECOVERY                                          │
  │  FOLLOW sets + structural delimiters                              │
  └────────────────────────────┬──────────────────────────────────────┘
                               │
  ┌────────────────────────────▼──────────────────────────────────────┐
  │  LAYER 6: SEMANTIC DISAMBIGUATION                                 │
  │  NFA-style multi-category parse + is_ground() + Ambiguous         │
  │  → Receives Layer 2.5's intra-category alternatives via spillover │
  │  → Weight-aware from_alternatives for tiebreaking                 │
  └────────────────────────────┬──────────────────────────────────────┘
                               │
                          Disambiguated AST
```

### Layer 2 → Layer 2.5

Layer 2 detects the ambiguity (multiple rules share first token) but cannot
resolve it. It flags the token group for NFA merged arm generation. Layer 2.5
generates the try-all mechanism that resolves the ambiguity by trying every
alternative.

### Layer 2.5 → Layer 3

Each alternative tried by the NFA merged arm runs its own Pratt infix loop
(Layer 3). The alternatives are independent: `FloatId(FloatVar("x"))` gets
its own infix context, `IntToFloat(IntVar("x"))` gets its own infix context,
etc. During forced-prefix replay, the complete parser (prefix + infix) runs
for each alternative, so Layer 3 operates correctly on each one.

### Layer 2.5 → Layer 6

Layer 2.5's spillover mechanism feeds directly into Layer 6's
`parse_preserving_vars`. The drain loop in `parse_preserving_vars` is the
bridge: it receives N-1 spilled intra-category alternatives and replays them
as full parses, adding them to the `successes` vector alongside cross-category
alternatives. The `AMBIGUOUS_WEIGHTS` thread-local carries the WFST weights
through to `from_alternatives()` for tiebreaking.

---

## 8. Source Map

| Concept                                | File                                 | Function / Lines                              |
|----------------------------------------|--------------------------------------|-----------------------------------------------|
| NFA-ambiguous category detection       | `prattail/src/trampoline.rs`         | `categories_needing_nfa_spillover()` (136–151) |
| RD rule grouping by dispatch token     | `prattail/src/trampoline.rs`         | `group_rd_by_dispatch_token()` (77–116)        |
| Public wrapper for pipeline access     | `prattail/src/trampoline.rs`         | `group_rd_by_dispatch_token_pub()` (118–125)   |
| NFA merged prefix arm generation       | `prattail/src/trampoline.rs`         | `write_nfa_merged_prefix_arm()` (162–361)      |
| NFA inline constructor                 | `prattail/src/trampoline.rs`         | `write_nfa_inline_constructor()` (367–444)     |
| Thread-local declarations (per-cat)    | `prattail/src/trampoline.rs`         | Lines 1082–1103                                |
| Forced-prefix check (trampoline)       | `prattail/src/trampoline.rs`         | Lines 1261–1277                                |
| Forced-prefix check (lazy parser)      | `prattail/src/trampoline.rs`         | Lines 3054–3066                                |
| Prefix match arm invocation            | `prattail/src/trampoline.rs`         | `write_prefix_match_arms()` (1288–1406)        |
| `TrampolineConfig.needs_nfa_spillover` | `prattail/src/trampoline.rs`         | Lines 665–669                                  |
| NFA spillover detection in pipeline    | `prattail/src/pipeline.rs`           | Lines 800–840                                  |
| CountingWeight ambiguity warnings      | `prattail/src/pipeline.rs`           | Lines 800–840                                  |
| `needs_nfa_spillover` configuration    | `prattail/src/pipeline.rs`           | Line 910                                       |
| WFST alternative ordering              | `prattail/src/wfst.rs`              | `nfa_alternative_order()` (198–218)            |
| Beam width application                 | `prattail/src/wfst.rs`              | `PredictionWfst::beam_width()` (175–191)       |
| `AMBIGUOUS_WEIGHTS` thread-local       | `macros/src/gen/runtime/language.rs` | Lines 1529–1535                                |
| Drain loop in `parse_preserving_vars`  | `macros/src/gen/runtime/language.rs` | Lines 1116–1161                                |
| Weight-aware `from_alternatives()`     | `macros/src/gen/runtime/language.rs` | Lines 284–326                                  |
| `BeamWidthConfig` enum                 | `prattail/src/lib.rs`               | Lines 76–123                                   |
