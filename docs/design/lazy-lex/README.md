# M2L — Lazy token-frontier lexing for the WPDA lattice backend

**Status:** implemented + verified + benchmarked (2026-06-17).
**Branch:** `feature/wfst-architecture` (worktree at `~9e547da2`).
**Relationship to the prior "Phase 2L STOP" verdict:** the HEAD commit
(`9e547da2`) recorded *"Phase 2L (lazy token frontier) — STOP by measurement"*
based on a since-deleted probe that measured eager-lex as 0.1–0.5 % of parse
time. This work is the **actual lazy implementation** the prior verdict deferred,
plus a rigorous before/after benchmark of both **time** and **space** (the prior
probe never measured the space / early-failure angle). The data both *confirms*
the prior time verdict in the aggregate **and** surfaces a real, statistically
significant time+space win on a specific input class the prior probe never
exercised (early-failure / first-token-reject).

---

## 1. What "lazy" means here

The eager lexer `lex_dag_core` (`prattail/src/runtime_types.rs`) worklist-builds
the **entire** token DAG — every `LexDagNode` + every lex-ambiguous alternative —
*before* the WPDA walker reads a single token. `LatticeTokenSource`
(`prattail/src/wpda_runtime.rs`) wraps that finished DAG; the walker reads it
through the `WpdaTokenSource` trait (`peek_kind` / `peek_text` /
`peek_alternatives` / `next_pos` / `end_byte` / `eof_node` / …), interpreting the
cursor `pos` as a **DAG node-id**.

`LazyLatticeTokenSource` (new) materializes each `LexDagNode` **on demand**
(memoized) when the walker first reads that node id. Positions the parser never
reaches are never lexed.

### Why node-id stability is the whole problem

The walker accesses nodes **by index**: `peek_kind(pos)`, `next_pos(pos,alt) →
target_node` (a node id), and forward look-aheads like `peek_kind(probe+1)`,
`peek_text(probe+2)` in the deterministic chain detectors
(`peek_binary_chain` / `peek_ternary_chain`). Those indices are *eager allocation
order*. So a lazy source that reordered ids — or returned a different
`target_node` integer — would break observational equivalence.

**Key invariant exploited:** eager `lex_dag_core` assigns node ids in **worklist
FIFO (BFS) order** seeded at byte 0; node `k`'s successors (hence the byte
positions of nodes `k+1, k+2, …`) are only discoverable by **expanding** node
`k`. Therefore node ids form a deterministic sequence fixed entirely by the BFS
expansion order. The lazy source replays the **identical** worklist discipline,
just *paused at the frontier*: it pumps the worklist only far enough to answer
the queries the walker actually makes. Same algorithm + same FIFO order ⇒ same
id assignment ⇒ every `WpdaTokenSource` observation is identical to eager, for
every reachable position. Unreached positions are simply never expanded.

This makes lazy **"prefix-lazy"**: answering a query about node `N` forces
expansion of nodes `0..=N` (you cannot know node `N`'s byte position without
expanding `0..N-1` to enqueue it). The benefit is realized exactly when the
walker stops querying node ids early — i.e. when it fails near the start of the
input.

---

## 2. Implementation

Three source files changed; one test + one bench added.

### 2.1 `expand_lex_node` extraction — `prattail/src/runtime_types.rs`

The per-node body of the `lex_dag_core` worklist loop (the DFA walk from a byte
position → surviving longest-per-kind edges + successor byte positions, including
the M6c.7.1 primary/secondary soft-fail logic and the M6c.8.1 EOF sentinel) is
factored into a reusable free function:

```rust
pub fn expand_lex_node<'a, T: Clone>(
    input: &'a str, start: usize, char_class: &[u8;256],
    dfa_next: &impl Fn(u32,u8)->u32, is_accepting: &impl Fn(u32)->bool,
    accept_alternatives: &impl Fn(u32,&'a str)->Vec<(T,f64)>,
    token_to_kind: &impl Fn(&T)->TokenKind, start_is_primary: bool,
) -> Result<ExpandedLexNode, String>
```

`ExpandedLexNode { byte_start, edges: Vec<RawLexEdge>, successors: Vec<LexSuccessor>, is_eof }`
carries everything the *caller's* worklist driver needs; `RawLexEdge` is a
`LexDagEdge` minus the `target_node` (resolved later). The edge survival filter
(longest-per-kind), edge ordering (longest-first), and successor ordering are
byte-identical to the inline loop.

Eager `lex_dag_core` was rewritten to call `expand_lex_node` inside its worklist
(the worklist discipline — seed `[0]`, skip-if-allocated, FIFO, global
`byte_to_node` enqueue dedup, EOF-first-writer-wins, primary-chain propagation —
stays in the eager driver). **Byte-identical output verified** by the existing
`lex_dag_core` unit tests (all 5 green) + the full prattail suite (3766 green).

### 2.2 `LazyLatticeTokenSource` — `prattail/src/wpda_runtime.rs`

- **Node storage:** a pre-sized `Vec<OnceLock<LexDagNode>>` of length
  `input.len()+1` (node count is bounded by `len+1` — ids are one per distinct
  worklist `start`, every `start` ∈ `{0} ∪ accept-end-bytes ⊆ 0..=len`). The
  pre-sized, never-resized `Vec` gives **stable addresses**, so `peek_text` /
  `peek_alternatives` can return borrowed slices — the same `OnceLock` trick the
  eager `LatticeTokenSource` already uses for its per-node secondary-alt cache.
- **Worklist bookkeeping** (`byte_to_node`, the pending FIFO, `primary_targets`,
  the EOF index, the id high-water mark) lives behind a single `RefCell`,
  mutated only transiently while pumping and released before any borrowed slice
  is handed out.
- **`pump_one()`** does exactly one worklist pop's worth of work (pop FIFO, skip
  if already allocated, expand via the boxed expander, assign the next id,
  materialize the node, enqueue successors with the global `byte_to_node` dedup +
  primary propagation). **`ensure_node(idx)`** pumps until id `idx` is
  materialized (or the worklist drains). **`ensure_byte_allocated(end_byte)`**
  pumps until that byte's id is known — this resolves `next_pos`/`target_node`
  on demand (lazy edges carry `target_node = UNRESOLVED`; lazy never reads it).
- **Type-erasure / closure plumbing:** the grammar's `Token<'a>` borrows the
  input, so it cannot satisfy a `T: 'static` bound. The generated `lex_dag_lazy`
  builds a boxed `NodeExpander = Box<dyn Fn(usize,bool) -> Result<ExpandedLexNode,String>>`
  that owns its **own copy** of the input and calls `expand_lex_node` with the
  grammar's free-`fn` closures baked in; the borrowed `Token<'a>` produced inside
  each call is consumed immediately by `token_to_kind` and never escapes. The
  source is constructed via `LazyLatticeTokenSource::from_expander(input, expander)`
  (a `from_lexer<T: 'static>` convenience also exists for owned-token test DFAs).

### 2.3 Generated entry — `prattail/src/automata/codegen.rs`

`write_lex_stream_via_core` now also emits, alongside `lex_dag`, a
`pub fn lex_dag_lazy(input: &str) -> LazyLatticeTokenSource` that builds the
boxed expander from the per-grammar `CHAR_CLASS` / `dfa_next` /
`is_accepting_state` / `accept_alternatives` / `token_to_kind`. Available on
every generated language (calculator, rhocalc, …).

### 2.4 The one subtlety that broke equivalence — `len()`

The generated cross-cat-LHS cast disambiguator
`prefix_crosscat_lhs_trigger_ahead` scans `for i in pos+1 .. tokens.len()`
looking ahead for a comparison trigger (e.g. `==` in `int(3) == 3`). If `len()`
under-reports, that scan stops early, the cast branch is never taken, and the
parse diverges (`int` collapses to a bare `PVar`). The first lazy `len()` (=
materialized count) caused exactly this divergence.

**Fix:** lazy `len()` returns the eager **full** node count by fully
materializing the DAG (memoized — drains once, then O(1)). The full lex is linear
in the input (the cheap part of parsing); what stays lazy is every parse the
walker abandons **before** any `len()`-bounded scan runs. `eof_node()` stays
lazy (returns `UNRESOLVED = usize::MAX` until the EOF node is materialized, which
happens exactly when a cursor reaches it — `pos == eof_node()` is then correct
in both regimes). This asymmetry is why first-token-reject inputs keep their
space win while inputs that hit the cast scan do not.

---

## 3. Correctness — lazy ≡ eager

`languages/tests/lazy_lex_equivalence.rs` (7 tests, all green) over both
calculator and rhocalc, two layers:

1. **Parse-result equivalence:** drive `parse_Proc_via_wpda_with_source` over an
   eager `LatticeTokenSource` and the lazy source; assert the realized term
   (`Debug`) and final cursor `pos` are identical (or, when eager hard-fails to
   lex, that lazy also fails to accept). Corpus = full-parse (`1 + 2 * 3`,
   `int(3) == 3`, `{0 | 1 | 2}`, `new(x,y) in { {x!(0) | y!(1)} }`, 20-term
   chains, …) **and** early-failure (long inputs with an error near the start:
   `1 + + + …`, `} } } …`, `int( …`, `* 1 + …`, `{0 | | | …`, `new new new …`).
2. **Per-position observation equivalence:** over a *fully-materialized* lazy
   source vs the eager DAG, assert `peek_kind` / `peek_text` /
   `peek_alternatives` (kind+text+end_byte per alt) / `is_ambiguous_at` /
   `end_byte` / `next_pos` / `position_order_key` / `eof_node` / `len` match for
   **every** node id. This is the direct node-id-stability proof.

Suites kept green with the unchanged eager path: `gen_calculator_unit` (169),
`gen_rhocalc_unit` (86), `rhocalc_tests` (10), `wpda_parity_rhocalc_collections`
(4), `wpda_parity_calculator` (52), `calculator` (100), `gen_calculator_analytical`
(16); prattail lib (3766). Zero regressions.

---

## 4. Benchmark — pgmcp experiment 69

`languages/examples/lazy_lex_bench.rs`. Protocol: release build, `taskset -c 2,3`
(single CCD), `performance` governor, 3 warm-ups, 60 samples/arm/input,
200 inner reps/sample (timer amortization). `lex_build_ns` = wall-time to
construct the token source **and** drive the WPDA parse end-to-end. Welch t,
one-sided H1: *lazy < eager*. Raw CSV + analysis in `docs/benchmarks/lazy-lex/`.

### TIME (per-input Welch — the aggregate masks the signal because inputs span 0.5 ms…13 ms)

| lang / class            | input                | eager mean | lazy mean | Δ      | p           |
|-------------------------|----------------------|-----------:|----------:|-------:|-------------|
| calculator / full       | every input (8/8)    |       —    |     —     | −4.3…−5.0 % | 1e-17…1e-22 **WIN** |
| calculator / earlyfail  | `}}}…` (first-tok)   |    37.5 µs |  10.2 µs  | **−72.7 %** | 2.7e-71 **WIN** |
| calculator / earlyfail  | `* 1 + …` (first-tok)|    49.9 µs |  10.4 µs  | **−79.3 %** | 6.3e-127 **WIN** |
| calculator / earlyfail  | `1 + + + …`          |   462.7 µs | 465.9 µs  | +0.7 % | NS (len()-scan) |
| calculator / earlyfail  | `int( …`             |   875.4 µs | 875.2 µs  | −0.0 % | NS (len()-scan) |
| rhocalc / full          | every input (4/4)    |       —    |     —     | +0.1…+1.0 % | NS (lazy slightly slower) |
| rhocalc / earlyfail     | `new new new…`       |    31.8 µs |   9.0 µs  | **−71.7 %** | 3.0e-128 **WIN** |
| rhocalc / earlyfail     | `{0 \| \| \| …`      |   308.8 µs | 278.3 µs  | −9.9 % | 2.0e-89 **WIN** |
| rhocalc / earlyfail     | `{ }}}…`             |    41.0 µs |  37.3 µs  | −9.0 % | 1.8e-68 **WIN** |

### SPACE (`lex_nodes_materialized`, eager vs lazy, same parse)

| lang / class           | aggregate saved | notable per-input |
|------------------------|----------------:|-------------------|
| calculator / full      | 0 % (95 = 95)   | lazy fully materializes (reaches EOF / len()-drain) |
| calculator / earlyfail | 47.1 % (153→81) | `}}}…` 37→1 (97 %), `* 1+…` 37→1 (97 %); `1++`/`int(` 0 % |
| rhocalc / full         | 0 % (77 = 77)   | — |
| rhocalc / earlyfail    | 55.6 % (99→44)  | `new new…` 21→2 (90 %), `{0\|\|\|…` 40→4 (90 %); `{ }}}` 0 % |

---

## 5. Honest read of the data

- **Does lazy win on time?** *Conditionally, yes.*
  - On **full-parse calculator** inputs lazy is **−4.5 % faster, p≈1e-20** on
    every input — a small but rock-solid win, attributable to avoiding eager's
    second global `target_node` fix-up pass (lazy resolves only the edges the
    walker actually traverses).
  - On **early-failure first-token-reject** inputs (both languages) lazy is
    **72–79 % faster, p<1e-70** — the walker dies after materializing 1–4 nodes
    instead of 21–40.
  - On **full-parse rhocalc** lazy is **~1 % slower** (RefCell/OnceLock
    indirection vs eager's flat `Vec`, not amortized away by the heavier parse).
  - On early-failure inputs that hit a `len()`-bounded look-ahead (`1 + + +`,
    `int(`) lazy is **neutral** (the cast/chain scan forces full materialization).
- **Does lazy win on space?** *Only on early-failure, and only when the walker
  rejects before any `len()`-bounded scan.* First-token-reject inputs save
  90–97 % of nodes; `len()`-scan inputs save 0 %; all full-parse inputs save 0 %
  (lazy fully materializes). Aggregate early-failure space saving ≈ 47–56 %.
- **Where the prior STOP verdict holds:** for the *typical* full-parse workload,
  lazy buys essentially nothing on space and ≤5 % on time — lexing is linear and
  the parse dominates, exactly as the 2026-06-17 measurement concluded. The new
  result is that lazy is **not** a pure non-goal: it is a real, significant win
  for **early-failure / malformed-input** workloads (IDE/LSP incremental typing,
  fuzzing, REPL typo recovery), where most lexing is wasted under the eager DAG.

The `len()` full-drain is the ceiling on the space win: any sound `len()`
requires knowing every node, and the generated cast disambiguator + the
deterministic parked-frontier guard both consult `len()`. Eliminating that
ceiling would require teaching those generated look-aheads to terminate at the
first `peek_kind(i) == None` (so they can run against a truly lazy `len()`); that
is a codegen change beyond this implementation's scope and is recorded here as
the next lever if early-failure space is prioritized.
