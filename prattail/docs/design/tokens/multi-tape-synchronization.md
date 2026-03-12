# Multi-Tape Synchronization for Token Streams

## 1. Intuition

A language with a single token stream is the common case: the lexer produces one
sequence of tokens and the parser consumes it. But real grammars often have
**multiple logically distinct streams**. Comments, whitespace, and documentation
annotations are lexed alongside code yet serve different consumers. PraTTaIL's
`-> stream_name` annotation in the `tokens { ... }` block routes tokens into
named auxiliary streams at lex time:

```
tokens {
    LineComment  = /\/\/[^\n]*/                -> comments;
    BlockComment = /\/\*([^*]|\*[^/])*\*\//   -> comments;
    Whitespace   = /[ \t\n\r]+/               -> ws;
    // All other tokens flow to "main" by default.
}
```

Once multiple streams exist, a natural question arises: *can we validate
cross-stream relationships at compile time?*

**Multi-tape automata** provide the formal model. Each stream becomes a *tape*
of a K-tape automaton. Cross-stream constraints become structural properties
checkable by reachability analysis. Think of a machine with K read heads, each
scanning its own tape. At every step the machine may advance any subset of heads
while the others remain stationary (reading epsilon). A transition fires only
when all K labels match the symbols under the corresponding heads. The weight on
each transition comes from a semiring -- typically `TropicalWeight`.

The key insight: **if the automaton has no reachable accepting state, the
cross-stream constraint is unsatisfiable and PraTTaIL emits a compile-time
diagnostic**. If accepting paths exist, the constraint is valid with zero
runtime cost.


## 2. Formal Definition

**Definition** (Weighted K-Tape Automaton). Over semiring (W, ⊕, ⊗, 0̄, 1̄):

    M = (Q, Σ₁ × Σ₂ × ··· × Σ_K ∪ {ε}, δ, I, F, W)

| Component | Meaning |
|-----------|---------|
| Q | Finite set of states |
| Σ_k | Alphabet of tape k, 1 ≤ k ≤ K |
| δ ⊆ Q × (Σ₁ ∪ {ε}) × ··· × (Σ_K ∪ {ε}) × Q × W | Weighted transition relation |
| I : Q → W | Initial weight function |
| F : Q → W | Final (accepting) weight function |

A transition (q, a₁, ..., a_K, q', w) reads symbol a_k from tape k (or ε if
a_k = None). The **acceptance weight** for input (w₁, ..., w_K) is:

    W(w₁, ..., w_K) = ⊕ over all accepting runs r of [⊗(weights along r) ⊗ F(q_final)]

For K = 1: weighted finite automaton. For K = 2: weighted finite-state
transducer (WFST). The implementation uses const generics:
`WeightedMultiTapeAutomaton<W, K>`.


## 3. Core Operations

Following Kempe (2004). Each operation preserves semiring structure.

### 3.1 pair(a₁, a₂) -- Two 1-Tape Automata to One 2-Tape Automaton

Given M₁ = (Q₁, Σ₁, δ₁, I₁, F₁) and M₂ = (Q₂, Σ₂, δ₂, I₂, F₂), the
**pair construction** produces product states Q₁ × Q₂ with three transition kinds:

```
Synchronized (both tapes advance):
    (q₁, q₂)  --[a, b] / w₁ ⊗ w₂-->  (q₁', q₂')

Epsilon-extended (tape 1 advances, tape 2 idle):
    (q₁, q₂)  --[a, ε] / w₁-->  (q₁', q₂)

Epsilon-extended (tape 2 advances, tape 1 idle):
    (q₁, q₂)  --[ε, b] / w₂-->  (q₁, q₂')
```

Initial: I(q₁, q₂) = I₁(q₁) ⊗ I₂(q₂). Accepting: F(q₁, q₂) = F₁(q₁) ⊗ F₂(q₂).

**Complexity**: O(|Q₁| · |Q₂| · (|δ₁| · |δ₂| + |δ₁| · |Q₂| + |Q₁| · |δ₂|)).

### 3.2 auto_intersect(i, j) -- Constrain Two Tapes to Match

Retains only transitions where labels[i] = labels[j]. States and weights are
preserved. This forces tapes i and j to read identical symbols at every step.

**Complexity**: O(|Q| + |δ|).

### 3.3 project(tape_idx) -- Extract Single-Tape Behavior

Produces a 1-tape automaton by keeping only the chosen tape's labels, replacing
all others with ε.

**Complexity**: O(|Q| + |δ|).

### 3.4 evaluate(inputs) -- BFS Over K Concrete Streams

```
1.  Seed: {(q, [0, ..., 0]) → I(q)} for each initial state q
2.  While queue non-empty:
      Pop (q, pos, w). For each transition (q, labels, q', w_t):
        For each tape k with labels[k] = Some(s):
          Require pos[k] < |inputs[k]| ∧ inputs[k][pos[k]] = s; advance pos[k]
        Accumulate: next[(q', pos')] ⊕= w ⊗ w_t
3.  Return ⊕{w ⊗ F(q) : (q, pos) where ∀k. pos[k] = |inputs[k]|}
```

**Complexity**: O(|Q| · ∏_k |inputs[k]| · |δ|).

### 3.5 multi_tape_intersect(a, b) -- Full K-Tape Product

Rabin--Scott product extended to K tapes. Product state (q_a, q_b) transitions
when both automata agree on all K labels. Weight: w_a ⊗ w_b.

**Complexity**: O(|Q_a| · |Q_b| · |δ_a| · |δ_b|).


## 4. The sync { ... } Constraint Block

When auxiliary streams exist, the grammar author may declare cross-stream
constraints in a `sync { ... }` block. Two constraint forms are supported:

### 4.1 align(stream_a, stream_b) on /pattern/

Boundary alignment. Positions where the boundary pattern appears in stream_a
must correspond to matching positions in stream_b. Implemented via
`auto_intersect(0, 1)` after `pair()`. Validation (`validate_sync_constraints()`):
both streams must exist, and the boundary pattern must appear in at least one
transition on each tape. If absent from either, the constraint is trivially
unsatisfiable.

### 4.2 track(auxiliary, primary)

Positional tracking. The auxiliary stream's token positions are recorded relative
to the primary stream. This is metadata only -- it does not structurally
constrain the automaton. Both stream names must exist.

### 4.3 Example

```
tokens {
    DocComment = /\/\/\/[^\n]*/  -> comments;
    Whitespace = /[ \t\n\r]+/   -> ws;
}

sync {
    align(comments, main) on /fn/;
    track(ws, main);
}
```

Doc-comment boundaries must align with `fn` tokens; whitespace positions are
tracked relative to main.


## 5. Pipeline Integration

Multi-tape synchronization is **compile-time only** -- zero runtime overhead.

```
                                        sync { ... } present?
                                             │
                                  ┌──────────┴──────────┐
                                  │                     │
                                 yes                    no
                                  │                     │
                       build_stream_automaton()   Analysis skipped
                       for each stream            (zero cost)
                                  │
                                  v
                        pair() ─── 2-tape product
                                  │
                                  v
                        Apply constraints:
                        Align → auto_intersect()
                        Track → metadata only
                                  │
                                  v
                        Reachability check
                                  │
                            ┌─────┴─────┐
                            │           │
                      satisfiable  unsatisfiable
                            │           │
                          (ok)     MT02-WARN diagnostic
```

When no `sync { ... }` block and no `-> stream` annotations exist, the
multi-tape module is never invoked. `LexResult.streams` remains an empty
`HashMap` (zero allocation).


## 6. build_synced_stream_automaton()

The K = 2 specialized entry point, invoked indirectly through `sync { ... }`.

```rust
pub fn build_synced_stream_automaton<W: Semiring>(
    stream_a:      &WeightedMultiTapeAutomaton<W, 1>,
    stream_b:      &WeightedMultiTapeAutomaton<W, 1>,
    stream_a_name: &str,
    stream_b_name: &str,
    sync:          &SyncSpec,
) -> SyncedStreamResult<W>
```

**Algorithm**:

1. **Combine** the two 1-tape automata via `pair()` → |Q_a| · |Q_b| states.
2. **Apply constraints** sequentially:
   - `Align`: verify boundary pattern in both streams, then `auto_intersect(0, 1)`.
   - `Track`: record in diagnostics (no structural modification).
   - Constraints referencing other stream pairs are skipped.
3. **Check satisfiability** via forward reachability from initial states.

**Returns** `SyncedStreamResult<W>`:

| Field | Type | Meaning |
|-------|------|---------|
| `automaton` | `WeightedMultiTapeAutomaton<W, 2>` | Synchronized 2-tape automaton |
| `constraint_diagnostics` | `Vec<Result<String, String>>` | Per-constraint Ok/Err messages |
| `is_satisfiable` | `bool` | All constraints admit ≥ 1 accepting path |


## 7. Diagram: 2-Tape Automaton (Main + Comments)

Main stream: `fn`, `foo`, `(`, `)`. Comment stream: `/// doc`. After `pair()`:

```
  Tape 0 (main):      fn    foo    (    )
  Tape 1 (comments):  /// doc

  ┌─────────┐  [fn, /// doc] / 1̄⊗1̄  ┌─────────┐  [foo, ε] / 1̄  ┌─────────┐
  │(q₀, r₀) │ ────────────────────> │(q₁, r₁) │ ──────────────> │(q₂, r₁) │
  └─────────┘                       └─────────┘                  └─────────┘
       │                                                              │
       │ [fn, ε] / 1̄                                    [(, ε] / 1̄
       v                                                              v
  ┌─────────┐  [foo, /// doc] / 1̄⊗1̄ ┌─────────┐                ┌─────────┐
  │(q₁, r₀) │ ────────────────────> │(q₂, r₁) │                │(q₃, r₁) │
  └─────────┘                       └─────────┘                └─────────┘
       │                                                              │
       │ [foo, ε] / 1̄                                   [), ε] / 1̄
       v                                                              v
  ┌─────────┐                                                   ┌─────────┐
  │(q₂, r₀) │  ···                                              │(q₄, r₁)*│
  └─────────┘                                                   └─────────┘

  q₀..q₄ = main states (5 boundaries, 4 tokens)
  r₀..r₁ = comment states (2 boundaries, 1 token)
  * = accepting (both tapes fully consumed)
```

After `auto_intersect(0, 1)` on boundary `fn`, synchronized transitions survive
only where both tapes read the same label. If `fn` never appears in the comment
stream, the Align constraint eliminates those transitions and may render the
automaton unsatisfiable -- producing a compile-time diagnostic.


## 8. Use Cases

**Doc-comment alignment.** `align(comments, main) on /fn/` verifies every
doc-comment cluster is followed by a function declaration. Misplaced doc-comments
are caught at compile time.

**Whitespace-sensitive parsing.** `track(ws, main)` correlates indentation tokens
with main-stream positions, enabling verification that nesting depth is
consistent with block structure.

**String interpolation.** `align` can verify that `{`/`}` pairs in an
interpolation sub-stream correspond to valid expression boundaries in the main
stream.

**Multi-channel process calculus.** In Rholang's `for (@x <- ch1, @y <- ch2)`,
each channel is a tape. `auto_intersect` enforces identical message sequences
when required; semiring weights encode priority or cost.


## 9. Complexity

Product state space grows as the product of per-tape state counts:

    |Q_product| = |Q₁| × |Q₂| × ··· × |Q_K|

For K = 2 with linear-chain stream automata (n = |tokens| + 1 states), the
product is O(|tokens₁| · |tokens₂|) -- manageable at compile time. For K > 2,
the current implementation defers to `validate_sync_constraints()`, which checks
constraints pairwise without the full product.

| Operation | Complexity |
|-----------|-----------|
| `pair(a₁, a₂)` | O(\|Q₁\| · \|Q₂\| · \|δ\|) |
| `auto_intersect(i, j)` | O(\|Q\| + \|δ\|) |
| `project(tape_idx)` | O(\|Q\| + \|δ\|) |
| `multi_tape_intersect(a, b)` | O(\|Q_a\| · \|Q_b\| · \|δ_a\| · \|δ_b\|) |
| `evaluate(inputs)` | O(\|Q\| · ∏_k \|inputs_k\| · \|δ\|) |
| `build_synced_stream_automaton` | O(\|Q_a\| · \|Q_b\| · \|δ\|) |
| `validate_sync_constraints` | O(C · \|tokens\|), C = constraint count |


## 10. Diagnostics

| Code | Severity | Trigger |
|------|----------|---------|
| MT01 | Warning | Two tapes constrained to identical patterns (redundant channel) |
| MT02 | Note | A tape has no `auto_intersect` constraints (disconnected) |
| MT03 | Info | A constraint is redundant (trivially satisfied) -- *planned* |

MT01 and MT02 are emitted by `analyze()` on the multi-tape automaton. MT03 is
planned for when an `Align` constraint does not reduce the transition count.


## 11. Feature Gate

```toml
[features]
multi-tape = ["wfst-log"]
```

All multi-tape code is gated behind `#[cfg(feature = "multi-tape")]`. When
disabled, `sync { ... }` is parsed but constraints are not validated. The feature
is included in the `predicated-types` and `full-analysis` groups.


## 12. References

1. Kempe, A. (2004). "Weighted Multi-Tape Automata and Transducers for NLP."
   *Finite-State Methods in NLP (FSMNLP)*. -- Defines `pair`, `project`, and
   `auto_intersect`.

2. Rabin, M.O. & Scott, D. (1959). "Finite Automata and Their Decision
   Problems." *IBM J. Research and Development*, 3(2), pp. 114--125. -- Product
   construction; decidability/undecidability boundary.

3. Mohri, M. (2009). "Weighted Automata Algorithms." *Handbook of Weighted
   Automata*, pp. 213--254. Springer. -- Semiring framework for weighted
   automata.
