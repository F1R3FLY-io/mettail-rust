# Stream-to-Lattice Conversion — Architecture

> **Code-path walkthrough** — Traces concrete source lines at each of the
> seven conversion points and five implicit lattice structures. For intuition
> and worked examples, see the
> [theory companion](../../theory/wfst/stream-to-lattice.md) first.

---

## Table of Contents

1. [Purpose and Scope](#1-purpose-and-scope)
2. [Conversion Point 1: lex_core()](#2-conversion-point-1-lex_core)
3. [Conversion Point 2: lex_weighted_core()](#3-conversion-point-2-lex_weighted_core)
4. [Conversion Point 3: lex_lattice_core()](#4-conversion-point-3-lex_lattice_core)
5. [Conversion Point 4: from_weighted()](#5-conversion-point-4-from_weighted)
6. [Conversion Point 5: resolve() / resolve_beam()](#6-conversion-point-5-resolve--resolve_beam)
7. [Conversion Point 6: viterbi_multi_step()](#7-conversion-point-6-viterbi_multi_step)
8. [Conversion Point 7: from_alternatives()](#8-conversion-point-7-from_alternatives)
9. [Implicit Lattice Structure Map](#9-implicit-lattice-structure-map)
10. [Complete Data Flow Diagram](#10-complete-data-flow-diagram)
11. [Source Map](#11-source-map)
12. [See Also](#12-see-also)

---

## 1. Purpose and Scope

This document traces the **concrete code paths** at each of PraTTaIL's seven
stream-to-lattice conversion points. Each section provides:

- Input and output types with generic parameters
- Key code snippets showing the conversion logic
- Data flow through function signatures
- Why that particular representation was chosen

**Prerequisite**: The [theory document](../../theory/wfst/stream-to-lattice.md)
provides intuition, worked examples, and the conversion catalog. This document
assumes familiarity with §3 (the seven conversion points) and §4 (the five
implicit lattices).

---

## 2. Conversion Point 1: `lex_core()`

**File**: `prattail/src/runtime_types.rs:241–348`

### Signature

```rust
pub fn lex_core<'a, T>(
    input: &'a str,
    file_id: Option<u32>,
    char_class: &[u8; 256],
    dfa_next: impl Fn(u32, u8) -> u32,
    is_accepting: impl Fn(u32) -> bool,
    accept_token: impl Fn(u32, &'a str) -> Option<T>,
) -> Result<(Vec<(T, Range)>, Position), String>
```

### Data Flow

```
 &str ──► byte loop ──► DFA walk ──► maximal-munch ──► Vec<(T, Range)>
              │              │              │
         char_class     dfa_next      accept_token
         [u8; 256]    (u32,u8)→u32   (u32,&str)→Option<T>
```

### Key Mechanics

1. **Byte-level DFA walk** (line 280–297): Each byte is mapped through
   `char_class` to an equivalence class, then `dfa_next(state, class)` produces
   the next state. Dead state = `u32::MAX`.

2. **Maximal-munch with backtracking** (line 274, 294–296): `last_accept`
   records `(state, pos, line, col)` at each accepting state. When the DFA
   dies, the lexer backtracks to `last_accept`.

3. **IS_ACCEPTING bitmap** (line 276, 294): The `is_accepting` callback is
   generated as a `u128` bitmap lookup for ≤128 states, or a `bool` array for
   larger DFAs (Sprint 1 perf optimization).

4. **Token emission** (line 305): `accept_token(state, text)` is called once
   per accepted span. Returns `None` to skip (e.g., comments).

### Lattice Capability

**None**. This function produces a flat `Vec<(T, Range)>` — no weights, no
alternatives. It is the zero-overhead baseline.

### Output Type

```
Ok((Vec<(T, Range)>, Position))
     │                    │
     │                    └─ final cursor position (for Eof token)
     └─ flat token stream
```

---

## 3. Conversion Point 2: `lex_weighted_core()`

**File**: `prattail/src/runtime_types.rs:356–465`

### Signature

```rust
pub fn lex_weighted_core<'a, T>(
    input: &'a str,
    file_id: Option<u32>,
    char_class: &[u8; 256],
    dfa_next: impl Fn(u32, u8) -> u32,
    is_accepting: impl Fn(u32) -> bool,
    accept_token: impl Fn(u32, &'a str) -> Option<T>,
    accept_weight: impl Fn(u32) -> f64,  // ← NEW
) -> Result<(Vec<(T, Range, f64)>, Position), String>
```

### Difference from `lex_core()`

Identical DFA walk. The only addition is `accept_weight(state)` (line 421),
called after `accept_token` succeeds. The weight is a compile-time constant
baked into generated code by the WFST pipeline.

### Weight Origin

```
Grammar DSL ──► Pipeline ──► PredictionWfst ──► codegen ──► accept_weight()
                                  │
                          WeightedAction.weight
                          (TropicalWeight)
```

The weight for each DFA accept state is the minimum WFST weight across all
rules that share that accept state. This is computed at compile time in
`pipeline.rs` and emitted as a `match state { ... }` in generated code.

### Lattice Capability

**Implicit only**. The flat stream carries weights that downstream conversion
points (④ `from_weighted`, ⑦ `from_alternatives`) use for disambiguation. The
weights encode WFST transition costs from the prediction automaton.

### Output Type

```
Ok((Vec<(T, Range, f64)>, Position))
     │                         │
     │                         └─ final cursor position
     └─ weighted token stream (weight per token)
```

---

## 4. Conversion Point 3: `lex_lattice_core()`

**File**: `prattail/src/runtime_types.rs:482–635`

### Signature

```rust
pub fn lex_lattice_core<'a, T: Clone>(
    input: &'a str,
    file_id: Option<u32>,
    char_class: &[u8; 256],
    dfa_next: impl Fn(u32, u8) -> u32,
    is_accepting: impl Fn(u32) -> bool,
    accept_alternatives: impl Fn(u32, &'a str) -> Vec<(T, f64)>,  // ← MULTI
) -> Result<(TokenSource<T, Range>, Position), String>
```

### Key Difference

The `accept_alternatives` callback returns **all** valid tokenizations at a
given DFA accept state, not just one. For multi-accept states (where the DFA
accepts into multiple token categories), it returns a `Vec<(T, f64)>` with
one entry per alternative.

### Two-Path Output

```rust
// Line 610–634
if !has_ambiguity {
    // Fast path: no lexical ambiguity — return Linear
    Ok((TokenSource::Linear(linear_tokens), eof_pos))
} else {
    // Slow path: construct TokenLattice DAG
    let num_nodes = token_alts.len() + 1;
    let mut lattice: TokenLattice<T, Range> = TokenLattice::with_capacity(num_nodes);
    lattice.ensure_nodes(num_nodes);
    for (i, ta) in token_alts.iter().enumerate() {
        for (token, weight) in &ta.alternatives {
            lattice.add_edge(i, i + 1, token.clone(), ta.range, TropicalWeight::new(*weight));
        }
    }
    Ok((TokenSource::Lattice(lattice), eof_pos))
}
```

### Ambiguity Detection

The `has_ambiguity` flag (line 499) is set to `true` the first time
`accept_alternatives` returns more than one alternative (line 574–576). Until
that happens, tokens accumulate in `linear_tokens` for zero-overhead return.

### DAG Construction (Slow Path)

```
Token position:    0        1        2       ...      N
Nodes:           ○───────○───────○───────    ──────○
                  │  alts  │  alts  │              │
                  ├───────►├───────►├──            ─►
                  ├───────►├───────►├──            ─►
                  └───────►└───────►└──            ─►
```

Node `i` = position before token `i`. Node `N` = after last token. Each
`token_alts[i]` adds one edge per alternative from node `i` to node `i+1`.
The edge carries `(token, range, TropicalWeight)`.

### Current Status

All current PraTTaIL grammars produce unambiguous DFAs (no multi-accept states),
so this function always returns `TokenSource::Linear`. The Lattice path is
compiled but never triggered.

---

## 5. Conversion Point 4: `from_weighted()`

**File**: `prattail/src/lattice.rs:150–153`

### Implementation

```rust
pub fn from_weighted(tokens: Vec<(T, S, f64)>) -> Self {
    let stripped: Vec<(T, S)> = tokens.into_iter().map(|(t, s, _w)| (t, s)).collect();
    TokenSource::Linear(stripped)
}
```

### Purpose

A backward-compatibility shim. When `lex_weighted_core()` was introduced, the
parser expected `Vec<(T, S)>`. This function strips weights and wraps the
result in `TokenSource::Linear`.

### Why It Always Returns Linear

The weighted lexer (conversion point ②) never produces lexical ambiguity —
it attaches a single weight to each token. Multi-accept ambiguity is handled
by `lex_lattice_core()` (conversion point ③), which returns `TokenSource`
directly. The `from_weighted` path is the non-lattice entry point.

### Data Flow

```
Vec<(T, S, f64)> ──► .map(|(t,s,_)| (t,s)) ──► TokenSource::Linear(Vec<(T,S)>)
```

---

## 6. Conversion Point 5: `resolve()` / `resolve_beam()`

**File**: `prattail/src/lattice.rs:162–198`

### `resolve()` — Unconditional Resolution

```rust
pub fn resolve(self) -> Result<Vec<(T, S)>, String> {
    match self {
        TokenSource::Linear(tokens) => Ok(tokens),       // identity
        TokenSource::Lattice(lattice) => {
            let final_node = lattice.num_nodes() - 1;
            match viterbi_best_path(&lattice, final_node) {
                Some(path) => Ok(path.tokens),
                None => Err("token lattice: final node unreachable".to_string()),
            }
        },
    }
}
```

### `resolve_beam()` — Beam-Pruned Resolution

```rust
pub fn resolve_beam(self, beam_width: Option<TropicalWeight>) -> Result<Vec<(T, S)>, String> {
    match self {
        TokenSource::Linear(tokens) => Ok(tokens),       // identity
        TokenSource::Lattice(lattice) => {
            let final_node = lattice.num_nodes() - 1;
            match viterbi_best_path_beam(&lattice, final_node, beam_width) {
                Some(path) => Ok(path.tokens),
                None => Err("...beam may be too narrow..."),
            }
        },
    }
}
```

### Branch on Variant

The parser calls `resolve()` **once** at entry. For `Linear`, this is an
identity operation — the `Vec` is moved out with zero cost. For `Lattice`,
Viterbi runs in O(V + E) to extract the minimum-weight path.

### Viterbi Algorithm

The `viterbi_best_path()` function (in `lattice.rs`) performs a forward DP:

```
dist[0] = TropicalWeight::one()   // zero cost
for node in 0..num_nodes:
    for edge in edges[node]:
        new_cost = dist[node] ⊗ edge.weight
        if new_cost < dist[edge.to]:
            dist[edge.to] = new_cost
            pred[edge.to] = (node, edge)
backtrace from final_node to 0 via pred[]
```

`viterbi_best_path_beam()` adds beam pruning: skip node `i` if
`dist[i] > dist[best_so_far] + beam_width`.

---

## 7. Conversion Point 6: `viterbi_multi_step()`

**File**: `prattail/src/recovery.rs:1054–1291`

### Signature

```rust
pub fn viterbi_multi_step(
    token_ids: &[TokenId],
    pos: usize,
    sync_tokens: &BTreeSet<TokenId>,
    config: &RecoveryConfig,
) -> Option<RepairSequence>
```

### Implicit Repair Lattice Topology

The function builds a forward trellis with `max_lookahead + 1` nodes. Node `i`
represents token position `pos + i`. The last node is SINK (the sync target).

```
         node 0       node 1       node 2       SINK
           │            │            │            │
   skip ───┼────────────►            │            │
   del  ───┼────────────►            │            │
   sub  ───┼────────────►            │            │
   ins  ───┼──────────────────────────────────────►
   swap ───┼─────────────────────────►            │
           │    skip ───┼────────────►            │
           │    sync ───┼─────────────────────────►
```

### Edge Types

| Edge Kind | `from → to` | Cost | Edit Count |
|-----------|-------------|------|------------|
| Skip | `i → i+1` | `config.skip_per_token` | 1 |
| Delete | `i → i+1` | `config.delete_cost` | `EditWeight::delete()` |
| Substitute | `i → i+1` | `config.substitute_cost` | `EditWeight::substitute()` |
| Swap | `i → i+2` | `config.swap_cost` | 1 |
| Insert | `i → SINK` | `config.insert_cost` | `EditWeight::insert()` |
| Sync | `i → SINK` | 0.0 (free) | 0 |

### Cost Type: RecoveryCost

```rust
type RecoveryCost = ProductWeight<TropicalWeight, EditWeight>;
```

This is a **Mode 2** semiring composition (see
[semiring-composition.md](../../theory/wfst/semiring-composition.md)):

- **Left** (TropicalWeight): Primary cost for Viterbi optimality
- **Right** (EditWeight): Edit count for human-readable diagnostics

The lexicographic ordering of `ProductWeight` means: minimize tropical cost
first, break ties by edit count.

### Forward DP (Lines 1094–1177)

```rust
for i in 0..max_lookahead {
    if dist[i].is_zero() { continue; }      // unreachable
    // Beam pruning (lines 1100-1104)
    if dist[i].left > dist[sink].left + beam { continue; }
    // Edge relaxation for each edge type...
    let new_cost = dist[i].times(&skip_edge);
    if new_cost < dist[i + 1] {
        dist[i + 1] = new_cost;
        pred[i + 1] = Some((i, RepairEdgeKind::Skip));
    }
    // ... similar for delete, substitute, swap, insert, sync
}
```

### Backtrace (Lines 1184–1240)

Walks `pred[]` backward from SINK to node 0, collecting `RepairAction` values.
The actions are reversed to produce a forward-ordered `RepairSequence`.

### Why Not `TokenLattice`?

The repair trellis has **fixed topology** (forward edges only, ≤32 nodes) and
uses `RecoveryCost` (a product semiring) rather than plain `TropicalWeight`.
Using stack-allocated arrays (`Vec<RecoveryCost>` with known max size) avoids
the overhead of `TokenLattice`'s heap-allocated adjacency lists and generic
DAG traversal.

---

## 8. Conversion Point 7: `from_alternatives()`

**File**: `macros/src/gen/runtime/language.rs:289–377`

### Generated Method (Conceptual)

```rust
fn from_alternatives(alts: Vec<Self>) -> Self {
    // 1. Flatten nested Ambiguous variants
    let flat: Vec<Self> = alts.into_iter().flat_map(|a| match a {
        Self::Ambiguous(inner) => inner,
        other => vec![other],
    }).collect();

    match flat.len() {
        0 => panic!("empty alternatives"),
        1 => flat.into_iter().next().unwrap(),
        _ => {
            let accepting: Vec<_> = flat.iter()
                .enumerate()
                .filter(|(_, a)| a.is_accepting())
                .collect();
            match accepting.len() {
                1 => /* Stage 1: single accepting → select it */,
                n if n > 1 => /* Stage 2: multiple accepting → WFST weight tiebreak */,
                _ => Self::Ambiguous(flat),  // Stage 3: no accepting
            }
        }
    }
}
```

### Three-Stage Disambiguation

| Stage | Condition | Resolution | Semiring Mode |
|-------|-----------|------------|---------------|
| 1 | Exactly one accepting alt | Select it directly | — |
| 2 | Multiple accepting alts | `min_by(WFST weight)` | Mode 3 (cross-structure) |
| 3 | Zero accepting alts | Return `Ambiguous(flat)` | — |

### Thread-Local Communication Channels

The disambiguation relies on three thread-local channels populated during
parsing:

| Channel | Type | Source | Purpose |
|---------|------|--------|---------|
| `AMBIGUOUS_WEIGHTS` | `Cell<Vec<f64>>` | `language.rs:1795` | WFST weights parallel to `successes` vec |
| `WEIGHT_CORRECTIONS` | `Cell<Vec<WeightCorrection>>` | `language.rs:1805` | C1 feedback: corrections when semantic pick ≠ weight-best |
| `NFA_PREFIX_SPILL_{CAT}` | `Cell<Vec<(Cat, usize, f64)>>` | `trampoline.rs:1920` | Spillover alternatives from NFA merged prefix |
| `NFA_FORCED_PREFIX_{CAT}` | `Cell<Option<(Cat, usize, f64)>>` | `trampoline.rs:1923` | Override: force specific prefix during replay |
| `NFA_PRIMARY_WEIGHT_{CAT}` | `Cell<f64>` | `trampoline.rs:1926` | Weight of the primary (initially returned) NFA result |

### Conceptual 2-Node Lattice

```
                    ╭── Alt₁ (w₁) ──╮
     parse point ───┤── Alt₂ (w₂) ──├─── result
                    ╰── Alt₃ (w₃) ──╯
```

This is a degenerate lattice with exactly two nodes (source and sink) and N
parallel edges. The "Viterbi" degenerates to `min_by(weight)` over accepting
alternatives.

### Weight Correction Recording (C1)

When the selected alternative differs from the weight-best overall alternative,
a `WeightCorrection` is pushed to `WEIGHT_CORRECTIONS`:

```rust
corrections.push(WeightCorrection {
    category: "Expr",
    primary_weight: weights[primary_idx],     // WFST's best
    selected_weight: weights[accepted_idx],   // semantically valid
    alternatives_considered: n_alts,
});
```

These corrections can be drained after parsing for offline weight training
feedback.

---

## 9. Implicit Lattice Structure Map

### Relationship Diagram

```
   ┌─────────────────────────────────────────────────────────────────────┐
   │                        COMPILE TIME                                │
   │                                                                    │
   │  ┌──────────────────┐     ┌──────────────────────┐                │
   │  │ E. WFST Transi-  │     │ C. Dispatch Weight   │                │
   │  │    tions          │────►│    Maps               │                │
   │  │ Vec<WfstState>    │     │ HashMap<(Cat,Tok),   │                │
   │  │ (wfst.rs)         │     │   Vec<Action>>       │                │
   │  └────────┬──────────┘     │ (pipeline.rs)        │                │
   │           │                └──────────┬───────────┘                │
   │           │                           │                            │
   │    ┌──────▼──────────┐         codegen bakes                      │
   │    │ D. Forward-     │         weights into                       │
   │    │    Backward Adj │         generated code                     │
   │    │ Vec<Vec<(usize, │                │                            │
   │    │   W)>>          │                │                            │
   │    │ (forward_       │                │                            │
   │    │  backward.rs)   │                │                            │
   │    └─────────────────┘                │                            │
   │     (wfst-log only)                   │                            │
   └───────────────────────────────────────┼────────────────────────────┘
                                           │
   ┌───────────────────────────────────────┼────────────────────────────┐
   │                        RUNTIME        │                            │
   │                                       ▼                            │
   │  ┌──────────────────────────────────────────────────┐             │
   │  │         Conversion Points ①②③ (Lexer)            │             │
   │  │    lex_core / lex_weighted / lex_lattice          │             │
   │  │                  (runtime_types.rs)                │             │
   │  └────────────────────────┬─────────────────────────┘             │
   │                           │                                        │
   │  ┌────────────────────────▼─────────────────────────┐             │
   │  │         Conversion Points ④⑤ (Resolution)        │             │
   │  │    from_weighted / resolve / resolve_beam          │             │
   │  │                  (lattice.rs)                      │             │
   │  └────────────────────────┬─────────────────────────┘             │
   │                           │                                        │
   │                    ┌──────▼──────┐                                 │
   │                    │   Parser    │                                 │
   │                    │  (RD/Pratt) │                                 │
   │                    └──┬──────┬───┘                                 │
   │                       │      │                                     │
   │            ┌──────────▼┐   ┌▼───────────────┐                     │
   │            │ A. Repair │   │ B. NFA Spill-  │                     │
   │            │   Trellis │   │    over Buffer  │                     │
   │            │ (recovery │   │ (trampoline.rs  │                     │
   │            │  .rs)     │   │  + language.rs) │                     │
   │            │  CP ⑥     │   │  CP ⑦           │                     │
   │            └───────────┘   └────────────────┘                     │
   └────────────────────────────────────────────────────────────────────┘
```

### Structure × Source File × Semantics

| Structure | Source File | Lines | Node Semantics | Edge Semantics |
|-----------|------------|-------|----------------|----------------|
| A. Recovery trellis | `recovery.rs` | 1054–1291 | Token positions after error | Repair actions (skip/del/sub/swap/ins/sync) |
| B. NFA spillover | `trampoline.rs` | 1920–1933 | Parse decision point | Alternative parse results with weights |
| C. Dispatch weights | `pipeline.rs` | codegen | Category × token pairs | Dispatch actions with WFST weights |
| D. Forward-backward | `forward_backward.rs` | 1–80 | WFST states | Transition weights (generic semiring) |
| E. WFST transitions | `wfst.rs` | 41–89 | Automaton states | `WeightedTransition` (input, output, weight) |

---

## 10. Complete Data Flow Diagram

End-to-end data flow from raw input to AST, with thread-local communication
channels annotated.

```
  Raw input (&str)
       │
       ▼
  ┌──────────────────────────────────────────────────┐
  │  Generated lex() function                        │
  │                                                  │
  │  ┌────────────┐  ┌──────────────┐  ┌──────────┐ │
  │  │ lex_core ① │  │lex_weighted②│  │lex_latt③│ │
  │  │ (no weight)│  │ (+ weight)   │  │(+ alts)  │ │
  │  └─────┬──────┘  └──────┬───────┘  └────┬─────┘ │
  └────────┼─────────────────┼───────────────┼───────┘
           │                 │               │
           │          from_weighted ④        │
           │          (strip weights)        │
           │                 │          resolve ⑤
           │                 │          (Viterbi)
           │                 │               │
           └────────┬────────┘───────────────┘
                    │
             Vec<(Token, Range)>
                    │
                    ▼
  ┌──────────────────────────────────────────────────┐
  │  Parser entry (parse_Cat)                        │
  │                                                  │
  │  Dispatch: match token {                         │
  │    token with single rule → deterministic arm    │
  │    token with N rules → NFA merged prefix        │
  │  }                                               │
  │                                                  │
  │  ┌──────────── NFA path ──────────────────────┐  │
  │  │                                            │  │
  │  │  AMBIGUOUS_WEIGHTS ◄── [w₁, w₂, ..., wₙ]  │  │
  │  │  (thread-local)                            │  │
  │  │                                            │  │
  │  │  Try alt₁ (weight-best) as primary         │  │
  │  │  Push alt₂..ₙ to NFA_PREFIX_SPILL          │  │
  │  │                                            │  │
  │  │  If primary not accepting:                 │  │
  │  │    Drain spill buffer (weight order)       │  │
  │  │    Replay with NFA_FORCED_PREFIX           │  │
  │  │    Short-circuit on first accepting        │  │
  │  │    Weight-threshold pruning (±2.0)         │  │
  │  │                                            │  │
  │  │  from_alternatives ⑦                       │  │
  │  │  ├─ Stage 1: single accepting → done       │  │
  │  │  ├─ Stage 2: multi accepting → weight min  │  │
  │  │  └─ Stage 3: none accepting → Ambiguous    │  │
  │  │                                            │  │
  │  │  WEIGHT_CORRECTIONS ◄── [correction, ...]  │  │
  │  │  (C1 feedback for training)                │  │
  │  └────────────────────────────────────────────┘  │
  │                                                  │
  │  ┌──────────── Error path ────────────────────┐  │
  │  │                                            │  │
  │  │  viterbi_multi_step ⑥                      │  │
  │  │  Build repair trellis (≤32 nodes)          │  │
  │  │  Edge costs: ProductWeight<Trop, Edit>     │  │
  │  │  Forward DP + backtrace → RepairSequence   │  │
  │  │  Apply repairs + re-parse                  │  │
  │  └────────────────────────────────────────────┘  │
  └──────────────────────────────────────────────────┘
                    │
                    ▼
                   AST
```

### Thread-Local Channel Summary

```
  AMBIGUOUS_WEIGHTS ─────────── parse entry → from_alternatives
  NFA_PREFIX_SPILL_{CAT} ────── trampoline NFA → language replay loop
  NFA_FORCED_PREFIX_{CAT} ───── replay loop → trampoline (override)
  NFA_PRIMARY_WEIGHT_{CAT} ──── trampoline → replay threshold calc
  RUNNING_WEIGHT_{CAT} ──────── trampoline → dispatch confidence
  PARENT_WEIGHT_{CAT} ───────── cross-category parse → child category
  WEIGHT_CORRECTIONS ────────── from_alternatives → training drain
```

---

## 11. Source Map

Every source file referenced in this document, with the relevant line ranges.

| File | Lines | Content |
|------|-------|---------|
| `prattail/src/runtime_types.rs` | 241–348 | `lex_core()` — unweighted DFA lexing |
| `prattail/src/runtime_types.rs` | 356–465 | `lex_weighted_core()` — weighted DFA lexing |
| `prattail/src/runtime_types.rs` | 482–635 | `lex_lattice_core()` — lattice-capable DFA lexing |
| `prattail/src/runtime_types.rs` | 638–640 | `is_whitespace()` — byte-level whitespace check |
| `prattail/src/lattice.rs` | 51–63 | `TokenSource` enum definition |
| `prattail/src/lattice.rs` | 150–153 | `from_weighted()` — strip weights to Linear |
| `prattail/src/lattice.rs` | 162–177 | `resolve()` — Viterbi on Lattice or identity on Linear |
| `prattail/src/lattice.rs` | 183–198 | `resolve_beam()` — beam-pruned Viterbi |
| `prattail/src/lattice.rs` | 246–249 | `TokenLattice` struct definition |
| `prattail/src/recovery.rs` | 1054–1291 | `viterbi_multi_step()` — implicit repair trellis |
| `prattail/src/recovery.rs` | 1301–1432 | `build_recovery_wfsts()` — discount/context injection |
| `macros/src/gen/runtime/language.rs` | 289–377 | `from_alternatives()` — NFA disambiguation |
| `macros/src/gen/runtime/language.rs` | 1795–1806 | `AMBIGUOUS_WEIGHTS`, `WEIGHT_CORRECTIONS` thread-locals |
| `prattail/src/trampoline.rs` | 1920–1933 | `NFA_PREFIX_SPILL`, `NFA_FORCED_PREFIX`, etc. thread-locals |
| `prattail/src/wfst.rs` | 41–56 | `WeightedTransition` struct |
| `prattail/src/wfst.rs` | 58–89 | `WfstState` struct |
| `prattail/src/wfst.rs` | 362–366 | `predict_with_confidence()` — CountingWeight annotation |
| `prattail/src/wfst.rs` | 422–428 | `confidence_gap()` — NbestWeight\<2\> gap |
| `prattail/src/forward_backward.rs` | 1–80 | `forward_scores()`, `backward_scores()` |
| `prattail/src/transducer.rs` | 107–148 | `DeadStateElimination` pass |

---

## 12. See Also

### Stream-to-Lattice Theory

- [Stream-to-Lattice — Theory](../../theory/wfst/stream-to-lattice.md):
  Pedagogical narrative, worked examples, conversion catalog, decision matrix

### Token Lattice Documentation

- [Token Lattices — Theory](../../theory/wfst/token-lattices.md): Formal DAG
  definition, Viterbi proofs, beam pruning
- [Token Lattices — Design](../../design/wfst/token-lattices.md): `TokenSource`
  enum design, generic parametrization
- [Token Lattices — Architecture](../../architecture/wfst/token-lattices.md):
  Pipeline integration, generated code anatomy

### Related Architecture Documentation

- [Pipeline Integration](pipeline-integration.md): WFST insertion point in the
  compile-time pipeline, step-by-step data flow
- [NFA Spillover Architecture](nfa-spillover-architecture.md): Demand-driven
  replay, weight-threshold pruning, acceptance short-circuit
- [Generated Code Anatomy](../generated-code-anatomy.md): Annotated walkthrough
  of generated parser code

### Related Theory Documentation

- [Semiring Composition](../../theory/wfst/semiring-composition.md): Three
  modes of multi-semiring interaction
- [Semirings](../../theory/wfst/semirings.md): Semiring axioms, all concrete
  weight types
- [Error Recovery Design](../../design/wfst/error-recovery.md): Recovery WFST
  construction, repair cost model
