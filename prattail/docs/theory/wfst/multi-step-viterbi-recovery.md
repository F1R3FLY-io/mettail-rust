# Multi-Step Viterbi Recovery Theory

**Date:** 2026-03-01

Formal mathematical foundations for `viterbi_multi_step()` and the
SwapTokens (transposition) repair action. The existing
[Viterbi and Forward-Backward](viterbi-and-forward-backward.md) document
covers Viterbi on the token *lattice* (lexer-level ambiguity); this
document covers Viterbi on the *repair lattice* (parser-level error
recovery).

---

## Table of Contents

1. [Motivation](#1-motivation)
2. [The Repair Lattice](#2-the-repair-lattice)
3. [Transposition as Edit Operation](#3-transposition-as-edit-operation)
4. [Viterbi on the Repair Lattice](#4-viterbi-on-the-repair-lattice)
5. [Backtrace and Sequence Reconstruction](#5-backtrace-and-sequence-reconstruction)
6. [Complexity Analysis](#6-complexity-analysis)
7. [Correctness](#7-correctness)
8. [Composite Repairs](#8-composite-repairs)
9. [Source Reference](#9-source-reference)
10. [References](#10-references)

---

## 1. Motivation

Single-step recovery (`find_best_recovery()`) evaluates each repair
action independently and returns the one with the lowest cost. This
produces a **locally optimal** repair: it finds the best single action,
but it cannot find the best *sequence* of actions.

Consider the token stream `[a, b, c, ;]` where `;` is a sync token and
the error is at position 0. Single-step evaluation:

| Strategy       | Action           | Cost |
|----------------|------------------|------|
| SkipToSync     | skip 3 to `;`    | 1.5  |
| DeleteToken    | delete `a`       | 1.0  |
| SubstituteToken| replace `a`      | 1.5  |
| InsertToken    | insert `;`       | 2.0  |

Single-step winner: DeleteToken (cost 1.0). But deleting `a` leaves
`[b, c, ;]` — the parser still faces `b` and `c` before the sync point.

Multi-step Viterbi evaluates the full sequence: delete `a`, skip `b`,
skip `c`, sync at `;` = 1.0 + 0.5 + 0.5 + 0.0 = 2.0. Compare with
pure skip: 0.5 + 0.5 + 0.5 + 0.0 = 1.5. The multi-step search finds
that pure skip (cost 1.5) beats delete+skip (cost 2.0), a comparison
single-step cannot make.

Multi-step recovery constructs a **repair lattice** and runs Viterbi to
find the globally optimal repair sequence.

---

## 2. The Repair Lattice

### 2.1 Nodes

Given an error at token position *pos* and remaining tokens
`remaining[0..L]` where *L* = min(|tokens| − *pos*, max_skip_lookahead):

```
Nodes: {0, 1, 2, ..., L−1, SINK}
```

- Node *i* represents token position *pos* + *i* in the original stream.
- **SINK** is a virtual node representing successful synchronization.

### 2.2 Six Edge Types

Each edge carries a tropical weight (lower is better).

| Edge Kind     | Source → Target  | Weight            | Guard                                   |
|---------------|------------------|-------------------|-----------------------------------------|
| Skip          | *i* → *i*+1      | c_skip            | *i* + 1 < |nodes|                       |
| Delete        | *i* → *i*+1      | c_delete          | *i* + 1 < |nodes|                       |
| Substitute    | *i* → *i*+1      | c_substitute      | token[*i*] ∉ sync_tokens                |
| Insert        | *i* → SINK       | c_insert          | ¬inserted[*i*] (max 1 per position)     |
| Swap          | *i* → *i*+2      | c_swap            | *i* + 2 ≤ *L*                           |
| Sync          | *i* → SINK       | 0                 | token[*i*] ∈ sync_tokens                |

**Weight functions** (tropical semiring: ⊕ = min, ⊗ = +):

```
w(Skip, i)       = c_skip           (default: 0.5)
w(Delete, i)     = c_delete         (default: 1.0)
w(Substitute, i) = c_substitute     (default: 1.5, for each sync_id)
w(Insert, i)     = c_insert         (default: 2.0, for each sync_id)
w(Swap, i)       = c_swap           (default: 1.25)
w(Sync, i)       = 0.0              (free transition to SINK)
```

All costs are parameterized via `RecoveryConfig`.

### 2.3 DAG Property

**Claim.** The repair lattice is a directed acyclic graph (DAG).

**Proof.** Consider the edges:

- Skip, Delete, Substitute: *i* → *i* + 1 (strictly increasing index).
- Swap: *i* → *i* + 2 (strictly increasing index).
- Sync: *i* → SINK (terminal node, no outgoing edges).
- Insert: *i* → SINK (terminal node, no outgoing edges).

The insert edge in the implementation is modeled as *i* → SINK (not a
self-loop *i* → *i*). The `inserted[i]` guard ensures at most one insert
per position. Since SINK has no outgoing edges, all paths terminate. No
edge decreases the node index, so no cycle exists.  ∎

**Note:** The conceptual model describes Insert as a self-loop
*i* → *i* with an inserted phantom token. The implementation realizes
this as an *i* → SINK edge (inserting a sync token at position *i*
directly reaches synchronization). The guard `inserted[i]` prevents
multiple inserts at the same position.

### 2.4 Repair Lattice Diagram

Five-node example with all edge types. Tokens: `[a, b, c, d, ;]`,
sync_tokens = {`;`}.

```
                    c_skip=0.5    c_skip=0.5    c_skip=0.5    c_skip=0.5
           ┌──────────────┬──────────────┬──────────────┬──────────────┐
           │              │              │              │              │
      ┌────▼───┐    ┌─────▼──┐    ┌─────▼──┐    ┌─────▼──┐    ┌─────▼──┐
      │  [0]   │    │  [1]   │    │  [2]   │    │  [3]   │    │  [4]   │
      │  "a"   │    │  "b"   │    │  "c"   │    │  "d"   │    │  ";"   │
      └──┬─┬───┘    └──┬─┬───┘    └──┬─┬───┘    └──┬─┬───┘    └────┬───┘
         │ │            │ │            │ │            │ │             │
         │ │ c_del=1.0  │ │ c_del=1.0  │ │ c_del=1.0  │ │ c_del=1.0  │ Sync
         │ └──────▶[1]  │ └──────▶[2]  │ └──────▶[3]  │ └──────▶[4]  │ (free)
         │              │              │              │              │
         │  c_swap=1.25 │  c_swap=1.25 │  c_swap=1.25 │              │
         └────────▶[2]  └────────▶[3]  └────────▶[4]  │              │
                                                       │              │
         c_ins=2.0      c_ins=2.0      c_ins=2.0      c_ins=2.0     │
         ─ ─ ─ ─ ▶ SINK ─ ─ ─ ─ ▶ SINK ─ ─ ─ ▶ SINK  ─ ─ ─ ▶ SINK │
                                                                      │
                                                               ┌──────▼──┐
                                                               │  SINK   │
                                                               └─────────┘
```

Substitute edges (omitted for clarity) connect *i* → *i* + 1 when
token[*i*] ∉ sync_tokens, with cost c_substitute for each sync token ID.

---

## 3. Transposition as Edit Operation

### 3.1 Damerau–Levenshtein Distance

The Damerau–Levenshtein distance *d_DL(a, b)* extends the Levenshtein
distance with a transposition operation on adjacent characters:

```
d_DL(a, b) = min operations to transform a into b using:
  - Insertion (cost 1)
  - Deletion (cost 1)
  - Substitution (cost 1)
  - Transposition of two adjacent characters (cost 1)
```

Transposition is a natural edit for keyboard typos: typing `ab` instead
of `ba` is a single finger-ordering error.

### 3.2 Cost Rationale

In PraTTaIL's repair lattice, swap cost is 1.25 (default), between
delete (1.0) and substitute (1.5):

| Repair    | Cost | Rationale                                           |
|-----------|------|-----------------------------------------------------|
| Delete    | 1.0  | Removes one token — information loss                |
| **Swap**  | 1.25 | Reorders two tokens — all information preserved     |
| Substitute| 1.5  | Replaces one token — information rewritten          |

Swap preserves both tokens (no information is created or destroyed),
justifying a cost between deletion (loses information) and substitution
(rewrites information). The 1.25 value was chosen empirically to be
preferred over substitute but not so cheap that it always wins over
delete.

### 3.3 Comparison with Delete+Insert

Without the swap edge, transposing two tokens requires delete + insert:

```
Swap:           cost = 1.25  (single edge, i → i+2)
Delete+Insert:  cost = 1.0 + 2.0 = 3.0  (two edges, i → i+1 → SINK)
```

The swap edge provides a 2.4× cost reduction for the same repair,
allowing the Viterbi search to strongly prefer transposition when the
swapped pair produces a valid continuation.

### 3.4 Worked Example

Input: `a b+` where the infix grammar expects `a +b` (operand operator
operand). Token stream at error:

```
remaining = [b, +, ...]
              0  1
```

- **Swap(0 → 2):** cost 1.25 — produces `+, b, ...` ; `+` is an
  infix operator (sync token), valid continuation.
- **Skip(0 → 1):** cost 0.5 — skips `b`, reaches `+` at position 1;
  but `b` is lost.
- **Delete(0 → 1):** cost 1.0 — deletes `b`, reaches `+`; but `b` is
  lost.

The swap edge is preferred when downstream simulation (Tier 3) confirms
that the swapped order is valid. The cost comparison:

| Strategy         | Cost | Information preserved? |
|------------------|------|-----------------------|
| Swap             | 1.25 | Yes (both tokens)     |
| Skip to `+`      | 0.5  | No (`b` lost)         |
| Delete `b`       | 1.0  | No (`b` lost)         |

Without Tier 3 simulation, skip (0.5) is cheaper than swap (1.25). With
Tier 3 validation confirming the swap produces a valid parse continuation,
the swap's cost is multiplied by the simulation discount (0.5×), giving
1.25 × 0.5 = 0.625, making it competitive with skip.

---

## 4. Viterbi on the Repair Lattice

### 4.1 Forward Pass

Compute the minimum cost to reach each node from node 0, processing
nodes in topological order (which is simply index order since the lattice
is a DAG).

```
dist[0] = 0.0    (tropical one = additive identity)
dist[i] = ∞      for i ≠ 0  (tropical zero = ∞)
```

For each node *i* = 0, 1, ..., *L* − 1:

```
  if dist[i] = ∞: continue   (unreachable)

  // Beam pruning
  if dist[SINK] ≠ ∞  and  dist[i] > dist[SINK] + beam_width:
    continue   (pruned)

  // Sync edge: i → SINK (free)
  if token[i] ∈ sync_tokens:
    relax(SINK, dist[i], (i, Sync(token[i])))

  // Skip edge: i → i+1
  relax(i+1, dist[i] + c_skip, (i, Skip))

  // Delete edge: i → i+1
  relax(i+1, dist[i] + c_delete, (i, Delete))

  // Substitute edge: i → i+1 (when token[i] ∉ sync_tokens)
  if token[i] ∉ sync_tokens:
    for sync_id ∈ sync_tokens:
      relax(i+1, dist[i] + c_substitute, (i, Substitute(sync_id)))

  // Swap edge: i → i+2
  if i + 2 ≤ L:
    relax(i+2, dist[i] + c_swap, (i, Swap))

  // Insert edge: i → SINK (max 1 per position)
  if ¬inserted[i]:
    for sync_id ∈ sync_tokens:
      relax(SINK, dist[i] + c_insert, (i, Insert(sync_id)))
      inserted[i] = true
```

Where `relax(target, new_cost, pred_info)`:

```
relax(target, new_cost, pred_info):
  if new_cost < dist[target]:
    dist[target] = new_cost
    pred[target] = pred_info
```

### 4.2 Predecessor Tracking

Each node records its predecessor for backtrace:

```
pred[i] = (predecessor_node, RepairEdgeKind)
```

The `RepairEdgeKind` enum captures all six edge types:

```
enum RepairEdgeKind {
    Skip,
    Delete,
    Substitute(TokenId),
    Insert(TokenId),
    Sync(TokenId),
    Swap,
}
```

### 4.3 Beam Pruning

When `beam_width` is `Some(w)`, the forward pass prunes nodes whose
accumulated cost exceeds `dist[SINK] + w`:

```
if dist[SINK] ≠ ∞  and  dist[i] > dist[SINK] + w:
  skip node i
```

This leverages the fact that any path through node *i* has cost ≥
dist[*i*], so if dist[*i*] already exceeds the best known path to SINK
by more than the beam width, no path through *i* can improve the result.

The default beam width is 3.0 (configurable via
`RecoveryConfig.beam_width`).

### 4.4 Pseudocode: Forward Pass + Backtrace

```
function viterbi_multi_step(token_ids, pos, sync_tokens, config):
    remaining = token_ids[pos..]
    L = min(|remaining|, config.max_skip_lookahead)
    if L = 0: return None

    // Initialize
    num_nodes = L + 1
    SINK = L
    dist[0..num_nodes] = [∞, ∞, ..., ∞]
    dist[0] = 0.0
    pred[0..num_nodes] = [None, None, ..., None]
    inserted[0..L] = [false, false, ..., false]
    beam = config.beam_width

    // Forward pass (§4.1)
    for i in 0..L:
        if dist[i] = ∞: continue
        if beam ≠ None and dist[SINK] ≠ ∞ and dist[i] > dist[SINK] + beam:
            continue
        // ... evaluate all edges from i (as in §4.1) ...

    if dist[SINK] = ∞: return None

    // Backtrace (§5)
    return backtrace(pred, SINK, pos, token_ids, dist[SINK])
```

---

## 5. Backtrace and Sequence Reconstruction

### 5.1 Walking the Predecessor Chain

Starting from SINK, walk `pred[]` backwards to node 0:

```
function backtrace(pred, SINK, pos, token_ids, total_cost):
    actions_reversed = []
    current = SINK
    sync_pos = pos

    while pred[current] ≠ None:
        (prev, edge_kind) = pred[current]
        match edge_kind:
            Sync(token_id):
                sync_pos = pos + prev
                current = prev
                if pred[prev] = None:
                    actions_reversed.push(SkipToSync(0, token_id))
                    break
            Skip:
                current = prev   // consolidated later
            Delete:
                actions_reversed.push(DeleteToken)
                current = prev
            Substitute(sync_id):
                actions_reversed.push(SubstituteToken(sync_id))
                current = prev
            Swap:
                actions_reversed.push(SwapTokens(pos+prev, pos+prev+1))
                current = prev
            Insert(sync_id):
                actions_reversed.push(InsertToken(sync_id))
                sync_pos = pos + prev
                current = prev
                if pred[prev] = None: break

    actions_reversed.reverse()
    return actions_reversed
```

### 5.2 Consolidating Consecutive Skips

Consecutive Skip edges are consolidated into a single `SkipToSync` action:

```
If the backtrace contains only Skip edges followed by a Sync edge:
    → SkipToSync { skip_count: number_of_skips, sync_token: token_at_sync }
```

This produces a human-readable diagnostic: "skip 3 token(s) to ';'"
rather than three separate skip actions.

### 5.3 Output: RepairSequence

```rust
struct RepairSequence {
    actions: Vec<RepairAction>,   // ordered atomic actions
    new_pos: usize,               // parser position after all repairs
    total_cost: TropicalWeight,   // tropical cost of entire sequence
    total_edits: EditWeight,      // edit-distance cost of sequence
}
```

When the sequence contains a single action, the caller may unwrap it
into a `RepairResult`. When it contains multiple actions, the caller
wraps it as `RepairAction::Composite { steps: actions }`.

---

## 6. Complexity Analysis

### 6.1 Time Complexity

The forward pass iterates over *L* = min(|remaining|,
max_skip_lookahead) nodes. At each node, it evaluates edges to at most
3 neighbors (skip/delete → *i* + 1, swap → *i* + 2, sync/insert → SINK)
plus substitute edges for each sync token.

```
T(L, |S|) = O(L × |S|)
```

where |*S*| = |sync_tokens| (number of substitute/insert candidates per
node). In practice, |*S*| ≤ 15 and *L* ≤ 32, giving at most ~480
edge relaxations.

### 6.2 Space Complexity

```
Space = O(L) for dist, pred, and inserted arrays
```

The `dist` and `pred` arrays each have *L* + 1 entries. The `inserted`
array has *L* entries. Total: 3*L* + 2 entries.

### 6.3 Beam Pruning Expected-Case Speedup

Without beam pruning, all *L* nodes are processed. With beam width *w*,
nodes whose accumulated cost exceeds the best SINK cost by more than *w*
are skipped. In practice, once a sync point is found (setting a finite
`dist[SINK]`), subsequent nodes far from any sync point are pruned.

Expected case: for an input with sync points distributed every *d*
tokens on average, approximately min(*L*, *d* + *w*/c_skip) nodes are
processed before the beam prunes the rest. For the default
*w* = 3.0 and c_skip = 0.5, this is *d* + 6 nodes.

---

## 7. Correctness

### 7.1 Theorem

`viterbi_multi_step` returns the minimum-cost repair sequence to any
reachable sync point within the lookahead window.

### 7.2 Proof

The proof relies on two properties: (1) the repair lattice is a DAG, and
(2) DAG relaxation in topological order computes exact shortest paths.

**Property 1 (DAG).** Proven in §2.3. All edges go from lower to higher
indices or to SINK (a terminal node).

**Property 2 (Topological-order relaxation).** In a DAG, processing
nodes in topological order guarantees that `dist[u]` is finalized before
any edge (u, v) is relaxed. This is the standard DAG shortest path
algorithm (Cormen et al., CLRS Ch. 24.2).

Since nodes are processed in index order 0, 1, ..., *L* − 1, and all
edges go from *i* to *j* with *j* > *i* or *j* = SINK, the topological
order property holds. Therefore, `dist[SINK]` at termination equals the
minimum-cost path from node 0 to SINK.

**Insert guard finiteness.** The `inserted[i]` flag ensures at most one
Insert edge per position. Since Insert edges go to SINK (terminal), they
cannot create cycles. Without the guard, the conceptual self-loop model
(Insert: *i* → *i*) would allow unbounded insertions. The guard ensures
the graph remains a DAG.  ∎

### 7.3 Insert Guard Necessity

Without the insert guard, an insert self-loop at position *i* would
create a cycle: *i* → *i* → *i* → ... . Although each traversal adds
*c_insert* > 0, the forward-pass algorithm processes each node once
(indexed loop), so the actual danger is not infinite cost reduction but
rather missing the self-loop relaxation on re-visit.

In the implementation, the insert edge goes directly to SINK (not back
to *i*), so cycles are structurally impossible. The `inserted[i]` guard
serves a secondary purpose: it prevents multiple insert edges from the
same position from competing (only the first insert-to-SINK edge is
considered, since subsequent inserts at the same position cannot improve
on the first — they have the same cost).

---

## 8. Composite Repairs

### 8.1 When Multi-Step Beats Single-Step

Multi-step Viterbi finds globally optimal sequences that combine
multiple repair types. Consider delete-then-skip vs. pure skip:

```
Delete at i, then skip from i+1 to sync:
  cost = c_delete + (k−1) × c_skip

Pure skip from i to sync:
  cost = k × c_skip
```

### 8.2 Break-Even Analysis

Delete+skip is cheaper than pure skip when:

```
c_delete + (k−1) × c_skip < k × c_skip
c_delete < c_skip
```

With defaults (c_delete = 1.0, c_skip = 0.5): 1.0 < 0.5 is **false**,
so pure skip is cheaper with default costs. However, when context
multipliers (Tier 1) increase skip costs:

```
c_delete × m_skip < c_skip × m_skip   (both multiplied by same factor)
```

This is never satisfied since both sides scale equally. But when Tier 3
simulation multipliers differ for delete vs. skip:

```
c_delete × m_tier3_delete < k × c_skip × m_tier3_skip
```

If deleting the error token leads to a valid continuation (m_tier3 =
0.5) while skipping does not (m_tier3 = 1.2), then:

```
1.0 × 0.5 < 3 × 0.5 × 1.2
0.5 < 1.8   ✓
```

The multi-step search discovers this interaction.

### 8.3 ProductWeight⟨TropicalWeight, EditWeight⟩

The `RepairSequence` tracks both tropical cost and edit distance:

```
total_cost  : TropicalWeight  (sum of tropical edge weights)
total_edits : EditWeight       (sum of edit distances per action)
```

These can be composed into a `ProductWeight⟨TropicalWeight, EditWeight⟩`
for joint optimization. Lexicographic ordering (tropical first, edit
second) ensures that the minimum-cost repair is preferred, with ties
broken by minimum edit distance.

---

## 9. Source Reference

| Symbol                 | Location                            |
|------------------------|-------------------------------------|
| `RepairEdgeKind`       | `prattail/src/recovery.rs:772–789`  |
| `RepairSequence`       | `prattail/src/recovery.rs:797–806`  |
| `viterbi_multi_step()` | `prattail/src/recovery.rs:840–1072` |
| `viterbi_recovery()`   | `prattail/src/recovery.rs:643–649`  |
| `viterbi_recovery_beam()` | `prattail/src/recovery.rs:656–764` |
| `RecoveryConfig`       | `prattail/src/recovery.rs:109–166`  |
| `RepairAction::SwapTokens` | `prattail/src/recovery.rs:266–271` |
| `RepairAction::Composite`  | `prattail/src/recovery.rs:277–280` |

---

## 10. References

- [Viterbi and Forward-Backward](viterbi-and-forward-backward.md) — Viterbi
  on the token lattice (different graph)
- [Semirings Overview](semirings.md) — tropical ⊕/⊗ operations
- [Extended Recovery Strategies](../../design/wfst/extended-recovery-strategies.md) —
  design-level integration of multi-step Viterbi
- [RecoveryConfig](../../design/wfst/recovery-config.md) — all cost parameters
- [Cascade Suppression](cascade-suppression.md) — absorbing-state model
  for cascade prevention

**External references:**

- Damerau, F. J. (1964). "A technique for computer detection and correction
  of spelling errors." *Communications of the ACM*, 7(3), 171–176.
- Cormen, T. H., Leiserson, C. E., Rivest, R. L., & Stein, C. (2009).
  *Introduction to Algorithms* (3rd ed.), Ch. 24.2: Single-source
  shortest paths in directed acyclic graphs.
- Mohri, M. (2009). "Weighted automata algorithms." In *Handbook of
  Weighted Automata*, Springer, pp. 213–254.
