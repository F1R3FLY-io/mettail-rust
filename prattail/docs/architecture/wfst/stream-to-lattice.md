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
10. [Weight Assignment Method Catalog](#10-weight-assignment-method-catalog)
11. [Complete Data Flow Diagram](#11-complete-data-flow-diagram)
12. [Source Map](#12-source-map)
13. [See Also](#13-see-also)

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
Token position:  0        1        2    ┅    N
Nodes:           ○────────○────────○──  ┅  ──○
                 │  alts  │  alts  │         │
                 ├───────►├───────►├──  ┅  ─►│
                 ├───────►├───────►├──  ┅  ─►│
                 └───────►└───────►└──  ┅  ─►│
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
        new_cost = dist[node] ⊗  edge.weight
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

| Edge Kind  | `from → to` | Cost                     | Edit Count                 |
|------------|-------------|--------------------------|----------------------------|
| Skip       | `i → i+1`   | `config.skip_per_token`  | 1                          |
| Delete     | `i → i+1`   | `config.delete_cost`     | `EditWeight::delete()`     |
| Substitute | `i → i+1`   | `config.substitute_cost` | `EditWeight::substitute()` |
| Swap       | `i → i+2`   | `config.swap_cost`       | 1                          |
| Insert     | `i → SINK`  | `config.insert_cost`     | `EditWeight::insert()`     |
| Sync       | `i → SINK`  | 0.0 (free)               | 0                          |

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

| Stage | Condition                 | Resolution               | Semiring Mode            |
|-------|---------------------------|--------------------------|--------------------------|
| 1     | Exactly one accepting alt | Select it directly       | —                        |
| 2     | Multiple accepting alts   | `min_by(WFST weight)`    | Mode 3 (cross-structure) |
| 3     | Zero accepting alts       | Return `Ambiguous(flat)` | —                        |

### Thread-Local Communication Channels

The disambiguation relies on three thread-local channels populated during
parsing:

| Channel                    | Type                              | Source               | Purpose                                                   |
|----------------------------|-----------------------------------|----------------------|-----------------------------------------------------------|
| `AMBIGUOUS_WEIGHTS`        | `Cell<Vec<f64>>`                  | `language.rs:1795`   | WFST weights parallel to `successes` vec                  |
| `WEIGHT_CORRECTIONS`       | `Cell<Vec<WeightCorrection>>`     | `language.rs:1805`   | C1 feedback: corrections when semantic pick ≠ weight-best |
| `NFA_PREFIX_SPILL_{CAT}`   | `Cell<Vec<(Cat, usize, f64)>>`    | `trampoline.rs:1920` | Spillover alternatives from NFA merged prefix             |
| `NFA_FORCED_PREFIX_{CAT}`  | `Cell<Option<(Cat, usize, f64)>>` | `trampoline.rs:1923` | Override: force specific prefix during replay             |
| `NFA_PRIMARY_WEIGHT_{CAT}` | `Cell<f64>`                       | `trampoline.rs:1926` | Weight of the primary (initially returned) NFA result     |

### Conceptual 2-Node Lattice

```
                    ╭── Alt₁ (w₁) ──╮
     parse point ───┼── Alt₂ (w₂) ──┼──▶ result
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
   ┌────────────────────────────────────────────────────────┐
   │                        COMPILE TIME                    │
   │                                                        │
   │  ┌───────────────────┐     ┌──────────────────────┐    │
   │  │ E. WFST Transi-   │     │ C. Dispatch Weight   │    │
   │  │    tions          │────►│    Maps              │    │
   │  │ Vec<WfstState>    │     │ HashMap<(Cat,Tok),   │    │
   │  │ (wfst.rs)         │     │   Vec<Action>>       │    │
   │  └────────┬──────────┘     │ (pipeline.rs)        │    │
   │           │                └──────────┬───────────┘    │
   │           ▼                           │                │
   │    ┌─────────────────┐         codegen bakes           │
   │    │ D. Forward-     │         weights into            │
   │    │    Backward Adj │         generated code          │
   │    │ Vec<Vec<(usize, │                │                │
   │    │   W)>>          │                │                │
   │    │ (forward_       │                │                │
   │    │  backward.rs)   │                │                │
   │    └─────────────────┘                │                │
   │     (wfst-log only)                   │                │
   └───────────────────────────────────────┊────────────────┘
                                           │
   ┌───────────────────────────────────────┊────────────────┐
   │                        RUNTIME        │                │
   │                                       ▼                │
   │  ┌──────────────────────────────────────────────────┐  │
   │  │         Conversion Points ①②③ (Lexer)            │  │
   │  │    lex_core / lex_weighted / lex_lattice         │  │
   │  │                  (runtime_types.rs)              │  │
   │  └────────────────────────┬─────────────────────────┘  │
   │                           │                            │
   │                           ▼                            │
   │  ┌──────────────────────────────────────────────────┐  │
   │  │         Conversion Points ④⑤ (Resolution)        │  │
   │  │    from_weighted / resolve / resolve_beam        │  │
   │  │                  (lattice.rs)                    │  │
   │  └────────────────────────┬─────────────────────────┘  │
   │                           │                            │
   │                           ▼                            │
   │                    ┌─────────────┐                     │
   │                    │   Parser    │                     │
   │                    │  (RD/Pratt) │                     │
   │                    └──┬──────┬───┘                     │
   │                       │      │                         │
   │                       ▼      ▼                         │
   │            ┌───────────┐   ┌─────────────────┐         │
   │            │ A. Repair │   │ B. NFA Spill-   │         │
   │            │   Trellis │   │    over Buffer  │         │
   │            │ (recovery │   │ (trampoline.rs  │         │
   │            │  .rs)     │   │  + language.rs) │         │
   │            │  CP ⑥     │   │  CP ⑦           │         │
   │            └───────────┘   └─────────────────┘         │
   └────────────────────────────────────────────────────────┘
```

### Structure × Source File × Semantics

| Structure           | Source File           | Lines     | Node Semantics              | Edge Semantics                               |
|---------------------|-----------------------|-----------|-----------------------------|----------------------------------------------|
| A. Recovery trellis | `recovery.rs`         | 1054–1291 | Token positions after error | Repair actions (skip/del/sub/swap/ins/sync)  |
| B. NFA spillover    | `trampoline.rs`       | 1920–1933 | Parse decision point        | Alternative parse results with weights       |
| C. Dispatch weights | `pipeline.rs`         | codegen   | Category × token pairs      | Dispatch actions with WFST weights           |
| D. Forward-backward | `forward_backward.rs` | 1–80      | WFST states                 | Transition weights (generic semiring)        |
| E. WFST transitions | `wfst.rs`             | 41–89     | Automaton states            | `WeightedTransition` (input, output, weight) |

---

## 10. Weight Assignment Method Catalog

This section catalogs all 14 weight assignment methods with their concrete
code paths. For formulae, rationale, and worked examples, see the
[theory companion §6](../../theory/wfst/stream-to-lattice.md#6-weight-assignment-methods).

### 10.1 Master Catalog

| ID | Method                   | Semiring             | Function                                              | File:Lines                    | Phase    |
|----|--------------------------|----------------------|-------------------------------------------------------|-------------------------------|----------|
| A1 | Lexical Priority Mapping | TropicalWeight       | `from_priority()`                                     | `semiring.rs:101–103`         | Compile  |
| A2 | Action Type Weight       | TropicalWeight       | `compute_action_weight()`                             | `wfst.rs:1264–1286`           | Compile  |
| A3 | Rule Specificity Weight  | TropicalWeight       | `specificity_weight()` + `compute_rule_specificity()` | `prediction.rs:1685–1701`     | Compile  |
| A4 | Dispatch Composition     | TropicalWeight       | `compute_composed_dispatch()`                         | `prediction.rs:1546`          | Compile  |
| A5 | Derivation Counting      | CountingWeight       | `predict_with_confidence()`                           | `wfst.rs:362–366`             | Compile  |
| A6 | Reachability Analysis    | BooleanWeight        | `detect_dead_rules()`                                 | `pipeline.rs:141`             | Compile  |
| A7 | Rule Context Tracking    | ContextWeight        | `ContextWeight::singleton()`                          | `semiring.rs:654`             | Compile  |
| A8 | Lookahead Bottleneck     | ComplexityWeight     | `ComplexityWeight::multi_lookahead()`                 | `semiring.rs:810–812`         | Compile  |
| A9 | N-Best Path Tracking     | NbestWeight\<N\>     | `NbestWeight::singleton()` + `confidence_gap()`       | `semiring.rs:1437–1441, 1487` | Compile  |
| B1 | Recovery Repair Costs    | TropicalWeight       | `RecoveryConfig` defaults                             | `recovery.rs:128–228`         | Runtime  |
| B2 | Edit Distance Counting   | EditWeight           | `skip/delete/insert/substitute()`                     | `semiring.rs:405–425`         | Runtime  |
| B3 | Dual-Cost Recovery       | ProductWeight\<T,E\> | `RecoveryCost` type alias                             | `recovery.rs:1054`            | Runtime  |
| B4 | Identity Assignment      | any W: Semiring      | `linear_to_lattice_generic()`                         | `lattice.rs:568–576`          | Runtime  |
| B5 | Position Weight Penalty  | TropicalWeight       | `POSITION_WEIGHT_PENALTY`                             | `wfst.rs:1124`                | Runtime  |
| C1 | Probabilistic Weights    | LogWeight            | `LogWeight::from_probability()`                       | `semiring.rs:936–939`         | Training |
| C2 | Entropy / Info Content   | EntropyWeight        | `EntropyWeight::from_arc_weight()`                    | `semiring.rs:1141`            | Training |

### 10.2 Compile-Time Code Paths

#### A1: Lexical Priority Mapping

```
TokenKind::priority() ──► TropicalWeight::from_priority(p) ──► accept_weight()
                                  │
                          w = 10.0 - p as f64
```

**Call chain**: Grammar DSL → `build_nfa()` (assigns priority per token) →
`minimize_dfa()` → `codegen.rs` emits `accept_weight(state)` match arm →
generated `lex_weighted_core()` calls `accept_weight` at each DFA accept.

**Key code** (`semiring.rs:101–103`):

```rust
pub fn from_priority(priority: u8) -> Self {
    TropicalWeight((10.0_f64) - priority as f64)
}
```

#### A2: Action Type Weight

```
DispatchAction variant ──► compute_action_weight() ──► WeightedAction.weight
```

**Call chain**: `pipeline.rs:build_prediction_wfsts()` iterates dispatch
actions → calls `compute_action_weight()` for each → stores in
`PredictionWfstBuilder` → `PredictionWfst.actions`.

**Key code** (`wfst.rs:1264–1286`):

```rust
fn compute_action_weight(
    _token_name: &str, action: &DispatchAction,
    _category: &str, _first_sets: &HashMap<String, FirstSet>,
    _overlaps: &HashMap<(String, String), CrossCategoryOverlap>,
    order: usize,
) -> TropicalWeight {
    match action {
        DispatchAction::Direct { .. } => TropicalWeight::new(0.0),
        DispatchAction::Grouping { .. } => TropicalWeight::new(0.0),
        DispatchAction::CrossCategory { needs_backtrack, .. } => {
            if *needs_backtrack { TropicalWeight::new(0.5) }
            else { TropicalWeight::new(0.0) }
        },
        DispatchAction::Cast { .. } => TropicalWeight::new(0.5),
        DispatchAction::Lookahead { .. } => TropicalWeight::new(1.0 + order as f64),
        DispatchAction::Variable { .. } => TropicalWeight::new(2.0),
    }
}
```

#### A3: Rule Specificity Weight

```
RuleInfo.first_items ──► compute_rule_specificity() ──► specificity_weight()
```

**Call chain**: `prediction.rs:compute_composed_dispatch()` → for each rule
matching a token, calls `compute_rule_specificity()` → passes result to
`specificity_weight()` → produces the `w_specificity` component.

**Key code** (`prediction.rs:1685–1701`):

```rust
fn compute_rule_specificity(rule: &RuleInfo) -> f64 {
    let mut terminals = 0.0;
    let mut nonterminals = 0.0;
    for item in &rule.first_items {
        match item {
            FirstItem::Terminal(_) => terminals += 1.0,
            FirstItem::NonTerminal(_) => nonterminals += 1.0,
            FirstItem::Ident => nonterminals += 0.5,
        }
    }
    terminals + 0.5 * nonterminals
}

fn specificity_weight(specificity: f64) -> f64 {
    1.0 / (1.0 + specificity)
}
```

#### A4: Dispatch Composition

```
w_action (A2) + w_specificity (A3) ──► w_final
```

**Call chain**: `prediction.rs:compute_composed_dispatch()` computes
`w_final = w_action + specificity_weight(compute_rule_specificity(rule))`
for each (category, token, rule) triple → stored in `ComposedEntry.weight` →
flows to `AMBIGUOUS_WEIGHTS` at runtime.

#### A5: Derivation Counting

```
PredictionWfst::predict(token) ──► .len() ──► CountingWeight::new(count)
```

**Call chain**: `wfst.rs:predict_with_confidence()` calls `predict()` →
counts results → annotates each action with `CountingWeight(count)`. Used by
pipeline diagnostics (W05 ambiguity warnings) when `count > 1`.

**Key code** (`wfst.rs:362–366`):

```rust
pub fn predict_with_confidence(&self, token_name: &str)
    -> Vec<(&WeightedAction, CountingWeight)>
{
    let actions = self.predict(token_name);
    let count = CountingWeight::new(actions.len() as u64);
    actions.into_iter().map(|a| (a, count)).collect()
}
```

#### A6: Reachability Analysis

```
categories + FIRST sets ──► fixed-point reachability ──► dead-rule warnings
```

**Call chain**: `pipeline.rs:detect_dead_rules()` builds reachable category set
via fixed-point → iterates `rule_infos` → rules in unreachable categories get
`DeadRuleWarning::UnreachableCategory`. Companion `detect_nearly_dead_paths()`
uses `ProductWeight<BooleanWeight, CountingWeight>` for joint
reachability + derivation count analysis.

#### A7: Rule Context Tracking

```
rule_label → label_id → ContextWeight::singleton(label_id) → ⊕  accumulation
```

**Call chain**: WFST construction assigns each rule label a unique `u8` ID →
`ContextWeight::singleton(id)` creates a 128-bit bitset with one bit set →
as WFST states are composed, `ContextWeight::plus()` (bitwise OR) accumulates
all contributing rule labels per state.

#### A8: Lookahead Bottleneck

```
dispatch_depth → ComplexityWeight::multi_lookahead(depth) → max along path
```

**Call chain**: During WFST construction, each dispatch arc is annotated with
its lookahead depth → `ComplexityWeight::times()` (= max) accumulates the
bottleneck complexity along paths → diagnostics report the maximum lookahead
depth encountered.

#### A9: N-Best Path Tracking

```
(path_id, weight) → NbestWeight::singleton(id, w) → merge → confidence_gap()
```

**Call chain**: `PredictionWfst::confidence_gap(token)` calls `predict()` →
computes gap between best and second-best weights → returned as `f64`.
Also available via `NbestWeight<N>::confidence_gap()` for generic N-best
tracking.

**Key code** (`wfst.rs:422–428`):

```rust
pub fn confidence_gap(&self, token_name: &str) -> f64 {
    let actions = self.predict(token_name);
    match (actions.first(), actions.get(1)) {
        (Some(best), Some(second)) => second.weight.value() - best.weight.value(),
        _ => f64::INFINITY,
    }
}
```

### 10.3 Runtime Code Paths

#### B1: Recovery Repair Costs

```
RecoveryConfig::default() ──► base costs ──► context multipliers ──► edge weights
```

**Call chain**: `recovery.rs:viterbi_multi_step()` receives `&RecoveryConfig` →
builds edge costs from `config.skip_per_token`, `config.delete_cost`, etc. →
applies tier-1 context multipliers (depth, BP, frame-kind) → applies tier-3
simulation multipliers → relaxes edges in forward DP.

**Key code** (`recovery.rs:201–228`):

```rust
impl Default for RecoveryConfig {
    fn default() -> Self {
        RecoveryConfig {
            skip_per_token: 0.5,
            delete_cost: 1.0,
            substitute_cost: 1.5,
            insert_cost: 2.0,
            swap_cost: 1.25,
            // ... context multipliers ...
        }
    }
}
```

#### B2: Edit Distance Counting

```
RepairAction kind ──► EditWeight::skip/delete/insert/substitute() ──► accumulate
```

**Call chain**: `recovery.rs:viterbi_multi_step()` creates
`ProductWeight<TropicalWeight, EditWeight>` edges → edit component tracks
discrete operation count → backtrace collects total edit count for diagnostics.

**Key code** (`semiring.rs:405–425`):

```rust
pub const fn skip() -> Self { EditWeight(1) }
pub const fn delete() -> Self { EditWeight(1) }
pub const fn insert() -> Self { EditWeight(2) }
pub const fn substitute() -> Self { EditWeight(2) }
```

#### B3: Dual-Cost Recovery

```
TropicalWeight (cost) ──┐
                         ├──► ProductWeight<TropicalWeight, EditWeight>
EditWeight (count) ─────┘
```

**Call chain**: `recovery.rs` defines `type RecoveryCost =
ProductWeight<TropicalWeight, EditWeight>` → Viterbi forward DP uses
`RecoveryCost::times()` for path extension and `RecoveryCost::plus()` for
alternative comparison → lexicographic `Ord` minimizes tropical first, then
edit count.

#### B4: Identity Assignment

```
Vec<(T, S)> ──► linear_to_lattice_generic::<W>() ──► TokenLattice<T, S, W>
                          │
                   edge weight = W::one()
```

**Call chain**: `lattice.rs:linear_to_lattice_generic()` iterates tokens →
`lattice.add_edge(i, i+1, token, span, W::one())` for each → produces a
linear chain lattice with identity weights.

**Key code** (`lattice.rs:568–576`):

```rust
pub fn linear_to_lattice_generic<T, S, W: Semiring>(tokens: Vec<(T, S)>)
    -> TokenLattice<T, S, W>
{
    let n = tokens.len();
    let mut lattice = TokenLattice::with_capacity(n + 1);
    lattice.ensure_nodes(n + 1);
    for (i, (token, span)) in tokens.into_iter().enumerate() {
        lattice.add_edge(i, i + 1, token, span, W::one());
    }
    lattice
}
```

#### B5: Position Weight Penalty

```
|alt_pos − primary_pos| × POSITION_WEIGHT_PENALTY ──► w_adjusted
```

**Call chain**: `trampoline.rs` NFA spillover replay → for each alternative
result, computes `|alt_pos - primary_pos|` → multiplies by
`POSITION_WEIGHT_PENALTY (0.5)` → adds to alternative's raw weight →
weight-threshold pruning uses adjusted weight for beam comparison.

**Key code** (`wfst.rs:1113–1124`):

```rust
/// C2: Position-aware NFA disambiguation — weight penalty per token difference.
///
/// adjusted_w = alt_w + |alt_pos - primary_pos| * penalty
pub const POSITION_WEIGHT_PENALTY: f64 = 0.5;
```

### 10.4 Training Code Paths (wfst-log gated)

#### C1: Probabilistic Weights

```
corpus ──► forward-backward ──► expected counts ──► SGD update ──► updated weights
```

**Call chain**: `training.rs:train_weights()` iterates corpus examples →
`forward_backward.rs:forward_scores()` + `backward_scores()` compute expected
counts under LogWeight → gradient = `expected_correct - expected_all` →
`weight -= learning_rate * gradient` → updated weights written back to
`PredictionWfst`. Corrections from `WEIGHT_CORRECTIONS` provide supervised
signal.

**Key code** (`semiring.rs:936–939`):

```rust
pub fn from_probability(p: f64) -> Self {
    assert!(p > 0.0, "LogWeight::from_probability: p must be > 0, got {p}");
    LogWeight(-p.ln())
}
```

#### C2: Entropy / Information Content

```
arc weights ──► EntropyWeight::from_arc_weight() ──► forward-backward ──► H(parse)
```

**Call chain**: `training.rs` constructs `EntropyWeight` for each WFST arc →
`forward_backward.rs` computes total expectation → final expectation = entropy
H in nats → drives adaptive beam width (low H → narrow beam, high H → wide
beam). Thresholds: `ENTROPY_BEAM_LOW_THRESHOLD = 0.5`,
`ENTROPY_BEAM_MAX = 10.0`.

**Key code** (`semiring.rs:1141`):

```rust
pub const fn from_arc_weight(weight: f64) -> Self {
    EntropyWeight { weight, expectation: weight }
}
```

### 10.5 Extended Source Map Entries

The following entries supplement the Source Map in [§12](#12-source-map) with
all weight-assignment-specific code locations.

| File                                | Lines     | Method | Content                                               |
|-------------------------------------|-----------|--------|-------------------------------------------------------|
| `prattail/src/automata/semiring.rs` | 101–103   | A1     | `TropicalWeight::from_priority()`                     |
| `prattail/src/wfst.rs`              | 1264–1286 | A2     | `compute_action_weight()`                             |
| `prattail/src/prediction.rs`        | 1685–1701 | A3     | `specificity_weight()` + `compute_rule_specificity()` |
| `prattail/src/prediction.rs`        | 1546      | A4     | `compute_composed_dispatch()`                         |
| `prattail/src/wfst.rs`              | 362–366   | A5     | `predict_with_confidence()`                           |
| `prattail/src/pipeline.rs`          | 141       | A6     | `detect_dead_rules()`                                 |
| `prattail/src/pipeline.rs`          | 450       | A6     | `detect_nearly_dead_paths()`                          |
| `prattail/src/automata/semiring.rs` | 654       | A7     | `ContextWeight::singleton()`                          |
| `prattail/src/automata/semiring.rs` | 810–812   | A8     | `ComplexityWeight::multi_lookahead()`                 |
| `prattail/src/automata/semiring.rs` | 1437–1441 | A9     | `NbestWeight::singleton()`                            |
| `prattail/src/automata/semiring.rs` | 1487      | A9     | `NbestWeight::confidence_gap()`                       |
| `prattail/src/wfst.rs`              | 422–428   | A9     | `PredictionWfst::confidence_gap()`                    |
| `prattail/src/recovery.rs`          | 128–228   | B1     | `RecoveryConfig` struct + `Default` impl              |
| `prattail/src/automata/semiring.rs` | 405–425   | B2     | `EditWeight::skip/delete/insert/substitute()`         |
| `prattail/src/recovery.rs`          | 1054      | B3     | `RecoveryCost` type alias                             |
| `prattail/src/lattice.rs`           | 568–576   | B4     | `linear_to_lattice_generic()`                         |
| `prattail/src/wfst.rs`              | 1124      | B5     | `POSITION_WEIGHT_PENALTY`                             |
| `prattail/src/automata/semiring.rs` | 936–939   | C1     | `LogWeight::from_probability()`                       |
| `prattail/src/automata/semiring.rs` | 1141      | C2     | `EntropyWeight::from_arc_weight()`                    |

---

## 11. Complete Data Flow Diagram

End-to-end data flow from raw input to AST, with thread-local communication
channels annotated.

```
  Raw input (&str)
       │
       ▼
  ┌────────────────────────────────────────────────────┐
  │  Generated lex() function                          │
  │                                                    │
  │  ┌────────────┐  ┌───────────────┐  ┌───────────┐  │
  │  │ lex_core ① │  │ lex_weighted② │  │ lex_latt③ │  │
  │  │ (no weight)│  │ (+ weight)    │  │ (+ alts)  │  │
  │  └─────┬──────┘  └───────┬───────┘  └─────┬─────┘  │
  └────────┊─────────────────┊────────────────┊────────┘
           │                 │                │
           │          from_weighted ④         │
           │          (strip weights)         │
           │                 │            resolve ⑤
           │                 │            (Viterbi)
           │                 │                │
           └────────┬────────┴────────────────┘
                    │
             Vec<(Token, Range)>
                    │
                    ▼
  ┌───────────────────────────────────────────────────┐
  │  Parser entry (parse_Cat)                         │
  │                                                   │
  │  Dispatch: match token {                          │
  │    token with single rule → deterministic arm     │
  │    token with N rules → NFA merged prefix         │
  │  }                                                │
  │                                                   │
  │  ┌──────────── NFA path ───────────────────────┐  │
  │  │                                             │  │
  │  │  AMBIGUOUS_WEIGHTS ◄── [w₁, w₂, ..., wₙ]    │  │
  │  │  (thread-local)                             │  │
  │  │                                             │  │
  │  │  Try alt₁ (weight-best) as primary          │  │
  │  │  Push alt₂..ₙ to NFA_PREFIX_SPILL           │  │
  │  │                                             │  │
  │  │  If primary not accepting:                  │  │
  │  │    Drain spill buffer (weight order)        │  │
  │  │    Replay with NFA_FORCED_PREFIX            │  │
  │  │    Short-circuit on first accepting         │  │
  │  │    Weight-threshold pruning (±2.0)          │  │
  │  │                                             │  │
  │  │  from_alternatives ⑦                        │  │
  │  │  ├─ Stage 1: single accepting → done        │  │
  │  │  ├─ Stage 2: multi accepting → weight min   │  │
  │  │  └─ Stage 3: none accepting → Ambiguous     │  │
  │  │                                             │  │
  │  │  WEIGHT_CORRECTIONS ◄── [correction, ...]   │  │
  │  │  (C1 feedback for training)                 │  │
  │  └─────────────────────────────────────────────┘  │
  │                                                   │
  │  ┌──────────── Error path ─────────────────────┐  │
  │  │                                             │  │
  │  │  viterbi_multi_step ⑥                       │  │
  │  │  Build repair trellis (≤32 nodes)           │  │
  │  │  Edge costs: ProductWeight<Trop, Edit>      │  │
  │  │  Forward DP + backtrace → RepairSequence    │  │
  │  │  Apply repairs + re-parse                   │  │
  │  └─────────────────────────────────────────────┘  │
  └───────────────────────────────────────────────────┘
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

## 12. Source Map

Every source file referenced in this document, with the relevant line ranges.

| File                                 | Lines     | Content                                                     |
|--------------------------------------|-----------|-------------------------------------------------------------|
| `prattail/src/runtime_types.rs`      | 241–348   | `lex_core()` — unweighted DFA lexing                        |
| `prattail/src/runtime_types.rs`      | 356–465   | `lex_weighted_core()` — weighted DFA lexing                 |
| `prattail/src/runtime_types.rs`      | 482–635   | `lex_lattice_core()` — lattice-capable DFA lexing           |
| `prattail/src/runtime_types.rs`      | 638–640   | `is_whitespace()` — byte-level whitespace check             |
| `prattail/src/lattice.rs`            | 51–63     | `TokenSource` enum definition                               |
| `prattail/src/lattice.rs`            | 150–153   | `from_weighted()` — strip weights to Linear                 |
| `prattail/src/lattice.rs`            | 162–177   | `resolve()` — Viterbi on Lattice or identity on Linear      |
| `prattail/src/lattice.rs`            | 183–198   | `resolve_beam()` — beam-pruned Viterbi                      |
| `prattail/src/lattice.rs`            | 246–249   | `TokenLattice` struct definition                            |
| `prattail/src/lattice.rs`            | 568–576   | `linear_to_lattice_generic()` — identity-weighted lattice   |
| `prattail/src/recovery.rs`           | 128–228   | `RecoveryConfig` struct + `Default` impl                    |
| `prattail/src/recovery.rs`           | 1054–1291 | `viterbi_multi_step()` — implicit repair trellis            |
| `prattail/src/recovery.rs`           | 1301–1432 | `build_recovery_wfsts()` — discount/context injection       |
| `prattail/src/automata/semiring.rs`  | 101–103   | `TropicalWeight::from_priority()` — A1                      |
| `prattail/src/automata/semiring.rs`  | 405–425   | `EditWeight::skip/delete/insert/substitute()` — B2          |
| `prattail/src/automata/semiring.rs`  | 654       | `ContextWeight::singleton()` — A7                           |
| `prattail/src/automata/semiring.rs`  | 810–812   | `ComplexityWeight::multi_lookahead()` — A8                  |
| `prattail/src/automata/semiring.rs`  | 936–939   | `LogWeight::from_probability()` — C1                        |
| `prattail/src/automata/semiring.rs`  | 1141      | `EntropyWeight::from_arc_weight()` — C2                     |
| `prattail/src/automata/semiring.rs`  | 1437–1441 | `NbestWeight::singleton()` — A9                             |
| `prattail/src/automata/semiring.rs`  | 1487      | `NbestWeight::confidence_gap()` — A9                        |
| `prattail/src/wfst.rs`               | 41–56     | `WeightedTransition` struct                                 |
| `prattail/src/wfst.rs`               | 58–89     | `WfstState` struct                                          |
| `prattail/src/wfst.rs`               | 362–366   | `predict_with_confidence()` — A5                            |
| `prattail/src/wfst.rs`               | 422–428   | `confidence_gap()` — A9                                     |
| `prattail/src/wfst.rs`               | 1124      | `POSITION_WEIGHT_PENALTY` — B5                              |
| `prattail/src/wfst.rs`               | 1264–1286 | `compute_action_weight()` — A2                              |
| `prattail/src/prediction.rs`         | 1546      | `compute_composed_dispatch()` — A4                          |
| `prattail/src/prediction.rs`         | 1685–1701 | `specificity_weight()` + `compute_rule_specificity()` — A3  |
| `prattail/src/pipeline.rs`           | 141       | `detect_dead_rules()` — A6                                  |
| `prattail/src/pipeline.rs`           | 450       | `detect_nearly_dead_paths()` — A6                           |
| `macros/src/gen/runtime/language.rs` | 289–377   | `from_alternatives()` — NFA disambiguation                  |
| `macros/src/gen/runtime/language.rs` | 1795–1806 | `AMBIGUOUS_WEIGHTS`, `WEIGHT_CORRECTIONS` thread-locals     |
| `prattail/src/trampoline.rs`         | 1920–1933 | `NFA_PREFIX_SPILL`, `NFA_FORCED_PREFIX`, etc. thread-locals |
| `prattail/src/forward_backward.rs`   | 1–80      | `forward_scores()`, `backward_scores()`                     |
| `prattail/src/transducer.rs`         | 107–148   | `DeadStateElimination` pass                                 |

---

## 13. See Also

### Stream-to-Lattice Theory

- [Stream-to-Lattice — Theory](../../theory/wfst/stream-to-lattice.md):
  Pedagogical narrative, worked examples, conversion catalog, decision matrix
- [Weight Assignment Methods — Theory](../../theory/wfst/stream-to-lattice.md#6-weight-assignment-methods):
  All 14 methods with formulae, rationale, examples, and diagrams

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
