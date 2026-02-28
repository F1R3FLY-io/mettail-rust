# Phase 6A: Multi-Accept DFA Construction

## 1. Problem

Standard subset construction collapses multi-accept NFA states into a single
winner by priority. When multiple NFA accept states converge in a single DFA
state -- as happens whenever a keyword like `error` also matches the identifier
pattern `[a-z]+` -- the traditional algorithm retains only the highest-priority
token kind and discards all alternatives.

This information loss is acceptable for a standalone lexer that always returns
the single "best" token. But in PraTTaIL, the parser performs context-sensitive
disambiguation at parse time: depending on the current grammar category, the
parser may need to re-interpret a keyword as an identifier (or vice versa).
Without the full set of alternative accepts, the parser has no way to recover
this information short of re-lexing, which defeats the purpose of a compiled
DFA lexer.

**Goal.** Extend the subset construction and Hopcroft minimization phases to
preserve ALL alternative accept tokens for ambiguous DFA states, while adding
zero overhead for unambiguous states.


## 2. Algorithm: Extended `resolve_accept()`

### 2.1. Context

During subset construction, each DFA state corresponds to a set of NFA states
(the "powerset"). When we create a new DFA state, we must determine its accept
status by examining the accept tokens of the constituent NFA states.

### 2.2. Standard Algorithm (Discards Alternatives)

The standard approach selects the single highest-priority accept:

```
resolve_accept(nfa, nfa_states):
    best_kind  := None
    best_weight := +inf
    for s in nfa_states:
        if nfa[s].accept is Some(kind):
            w := nfa[s].weight
            if w < best_weight:
                best_kind   := kind
                best_weight := w
    return (best_kind, best_weight)
```

### 2.3. Extended Algorithm (Preserves All Alternatives)

The extended algorithm collects ALL distinct `TokenKind` values, deduplicates
them by kind, and retains the best weight per kind:

```
resolve_accept(nfa, nfa_states) -> ResolvedAccept:
    by_kind : BTreeMap<TokenKind, TropicalWeight> := {}

    /* Step 1: Collect all accepting (kind, weight) pairs.
       Keep the minimum weight per kind. */
    for s in nfa_states:
        if nfa[s].accept is Some(kind):
            w := nfa[s].weight
            if kind in by_kind:
                by_kind[kind] := min(by_kind[kind], w)
            else:
                by_kind[kind] := w

    if by_kind is empty:
        return ResolvedAccept { kind: None, weight: +inf, alt_accepts: [] }

    /* Step 2: Sort alternatives by weight ascending (best first). */
    alts := by_kind.into_sorted_vec()     /* Vec<(TokenKind, TropicalWeight)> */
    sort alts by weight ascending

    /* Step 3: Primary accept = first element (lowest weight = highest priority). */
    primary_kind   := alts[0].kind
    primary_weight := alts[0].weight

    /* Step 4: Populate alt_accepts only when 2+ distinct kinds exist. */
    alt_accepts := if |alts| >= 2 then alts else []

    return ResolvedAccept {
        kind:        Some(primary_kind),
        weight:      primary_weight,
        alt_accepts: alt_accepts,
    }
```

### 2.4. Key Properties

| Property | Description |
|---|---|
| **Primary unchanged** | `DfaState.accept` and `DfaState.weight` are identical to the standard algorithm. Existing code that only reads `accept` is unaffected. |
| **Deduplication by kind** | If multiple NFA states produce the same `TokenKind`, only the best (lowest) weight is kept for that kind. |
| **Sorted by weight** | `alt_accepts` is sorted ascending by tropical weight, so `alt_accepts[0]` is always the primary winner. The parser can iterate from index 1 to find fallback alternatives. |
| **Empty when unambiguous** | `alt_accepts` is the empty `Vec` when 0 or 1 distinct `TokenKind`s exist, adding zero allocation overhead for unambiguous states. |

### 2.5. Data Structures

```rust
/// Resolved accept information for a set of NFA states.
pub(crate) struct ResolvedAccept {
    /// Primary accept (lowest weight = highest priority), or None.
    pub kind: Option<TokenKind>,
    /// Weight of the primary accept. TropicalWeight::zero() (infinity) if no accept.
    pub weight: TropicalWeight,
    /// All alternative accepts (including the primary), sorted by weight ascending.
    /// Empty if 0 or 1 accepting NFA states (unambiguous).
    pub alt_accepts: Vec<(TokenKind, TropicalWeight)>,
}

/// DFA state with deterministic transitions.
pub struct DfaState {
    /// Dense transition table: transitions[class_id] = target_state.
    /// DEAD_STATE means no transition for that equivalence class.
    pub transitions: Vec<StateId>,
    /// If this is an accepting state, which token kind it produces (primary winner).
    pub accept: Option<TokenKind>,
    /// Tropical weight for this accepting state.
    /// Lower weight = higher priority.
    pub weight: TropicalWeight,
    /// Alternative accept tokens for this DFA state, sorted by weight (ascending).
    /// Non-empty only for ambiguous states where 2+ distinct TokenKinds are valid.
    pub alt_accepts: Vec<(TokenKind, TropicalWeight)>,
}
```

The `DfaState` provides convenience methods for querying ambiguity:

```rust
impl DfaState {
    /// Whether this state has ambiguous accepts (2+ distinct token kinds).
    pub fn is_ambiguous(&self) -> bool {
        !self.alt_accepts.is_empty()
    }
}

impl Dfa {
    /// Whether any DFA state has ambiguous accepts.
    pub fn has_ambiguous_accepts(&self) -> bool {
        self.states.iter().any(|s| s.is_ambiguous())
    }

    /// Collect all ambiguous DFA states: (state_id, alt_accepts_slice).
    pub fn ambiguous_states(&self) -> Vec<(StateId, &[(TokenKind, TropicalWeight)])> { ... }
}
```


## 3. Hopcroft Minimization with Multi-Accept Partition Keys

### 3.1. Standard Minimization Partition Key

In standard Hopcroft minimization, the initial partition groups DFA states by
their accept status:

```
partition_key(state) = (state.accept, state.transitions)
```

States with the same `accept` and identical transitions on all equivalence
classes are merged into a single minimized state. This is correct for
single-accept DFAs: if two states produce the same token, they are
indistinguishable from the lexer's perspective.

### 3.2. Problem with Multi-Accept

Consider two DFA states after subset construction:

| State | `accept` | `alt_accepts` |
|---|---|---|
| q7 | `Fixed("error")` | `[(Fixed("error"), 0.0), (Ident, 9.0)]` |
| q12 | `Fixed("error")` | `[]` (unambiguous) |

Under standard minimization, both states have `accept = Some(Fixed("error"))`,
so they would be placed in the same initial partition and potentially merged.
But merging would destroy q7's alternative accept information -- the parser
would lose the ability to re-interpret `error` as an identifier in contexts
where no `error` keyword is expected.

### 3.3. Extended Partition Key

The extended partition key includes `alt_accepts` as a distinguishing component:

```
partition_key(state) = (state.accept, state.weight, state.alt_accepts, state.transitions)
```

Concretely, the implementation uses a `BTreeMap` with a composite key type:

```rust
type PartitionKey<'a> = (
    Option<&'a TokenKind>,          // primary accept
    u64,                            // weight as f64 bit pattern (total ordering)
    Vec<(&'a TokenKind, u64)>,      // alt_accepts as (kind, weight_bits)
);
```

States with different alternative accept sets are placed in separate initial
partitions, even if they share the same primary accept token. This guarantees
they are never merged by the refinement loop.

### 3.4. Correctness Argument

**Claim.** Extending the partition key with `alt_accepts` preserves the
Hopcroft invariant: states in the same partition are observationally
indistinguishable.

**Proof sketch.**

1. **Refinement monotonicity.** The extended key produces a *finer* initial
   partition than the standard key (strictly more partitions, or the same).
   Hopcroft refinement only ever splits partitions, never merges them.
   Therefore, the extended minimization produces a DFA that is no larger than
   the input, and potentially slightly larger than the standard minimization.

2. **Soundness.** Two states in the same partition have identical `accept`,
   `weight`, `alt_accepts`, and transition behavior on all equivalence classes.
   They are fully interchangeable from both the lexer's and parser's
   perspective.

3. **Preservation.** No ambiguous state is merged with a non-ambiguous state
   (different `alt_accepts` lengths), and no two ambiguous states with
   different alternative sets are merged (different `alt_accepts` contents).

### 3.5. Minimized DFA Construction

When building the minimized DFA from partitions, each new state inherits the
representative's full metadata including `alt_accepts`:

```rust
let rep = partitions[part_idx][0];
let new_state = new_dfa.add_state(DfaState {
    transitions: vec![DEAD_STATE; num_classes],
    accept:      dfa.states[rep as usize].accept.clone(),
    weight:      dfa.states[rep as usize].weight,
    alt_accepts: dfa.states[rep as usize].alt_accepts.clone(),
});
```

The subsequent BFS canonical state reordering (`canonicalize_state_order`)
likewise propagates `alt_accepts` to the reordered states.


## 4. Worked Example

### 4.1. Grammar

Consider a grammar with:
- Keyword terminal: `error` (produces `Fixed("error")`, priority 10)
- Identifier pattern: `[a-z]+` (produces `Ident`, priority 1)

### 4.2. Priority and Weight Mapping

Token priorities map to tropical weights via `weight = 10.0 - priority`:

| TokenKind | Priority | Tropical Weight |
|---|---|---|
| `Fixed("error")` | 10 | 0.0 |
| `Ident` | 1 | 9.0 |

Lower weight = higher priority. The tropical semiring `plus` operation (min)
selects `Fixed("error")` when both converge.

### 4.3. NFA Construction

The NFA has two parallel recognition paths from the global start state:

```
                    ┌─────────────── Keyword trie path ──────────────────┐
                    │                                                     │
  NFA start ──eps──>├──'e'──>q1──'r'──>q2──'r'──>q3──'o'──>q4──'r'──>q5│
     (q0)          │   accept: Fixed("error"), weight: 0.0              │
                    │                                                     │
                    ├─────────────── Ident regex path ───────────────────┤
                    │                                                     │
                    └──eps──>q6──[a-z]──>q7─┐                            │
                              accept: Ident │                            │
                              weight: 9.0   │                            │
                                    ┌───────┘                            │
                                    │ [a-z] (self-loop)                  │
                                    └──>q7                               │
```

After lexing the input `"error"`:

- The keyword path arrives at NFA state q5 with `accept: Fixed("error"),
  weight: 0.0`.
- The identifier path arrives at NFA state q7 with `accept: Ident,
  weight: 9.0` (having consumed five `[a-z]` characters).

### 4.4. Subset Construction

During subset construction, the DFA state after consuming `"error"` corresponds
to the NFA state set `{q5, q7}`. The extended `resolve_accept` processes this:

1. **Collect:** `by_kind = { Fixed("error"): 0.0, Ident: 9.0 }`
2. **Sort:** `alts = [(Fixed("error"), 0.0), (Ident, 9.0)]`
3. **Primary:** `kind = Fixed("error")`, `weight = 0.0`
4. **Alt accepts:** `|alts| = 2 >= 2`, so `alt_accepts = [(Fixed("error"), 0.0), (Ident, 9.0)]`

The resulting DFA state:

```
    DFA state d_error:
        accept:      Some(Fixed("error"))
        weight:      TropicalWeight(0.0)
        alt_accepts: [(Fixed("error"), 0.0), (Ident, 9.0)]
```

### 4.5. DFA Diagram

```
                                     e           r           r           o           r
  d0 ─────────> d1 ─────────> d2 ─────────> d3 ─────────> d4 ─────────> d5
  start       [a-z]         [a-z]         [a-z]         [a-z]         [a-z]
  (no accept)  Ident         Ident         Ident         Ident        ╔═══════════════╗
               w=9.0         w=9.0         w=9.0         w=9.0        ║  accept:       ║
                 │             │             │             │           ║  Fixed("error")║
                 │             │             │             │           ║  w=0.0         ║
                 │             │             │             │           ║  alt_accepts:  ║
                 │             │             │             │           ║  [Fixed, Ident]║
                 │             │             │             │           ╚═══════════════╝
                 │             │             │             │                  │
                 └─[a-z]──>d_ident   (all [a-z] self-loops on d_ident)      │
                           Ident                                            │
                           w=9.0              <───── [a-z] ─────────────────┘
                           alt_accepts=[]             (continues to d_ident)
```

Key observations:

- States d1 through d4 accept `Ident` only (the keyword path has not yet
  completed). These are unambiguous: `alt_accepts = []`.
- State d5 is the **ambiguous** state after `"error"`: both the keyword path
  and the identifier path have completed. It has `alt_accepts` with both kinds.
- Consuming any additional `[a-z]` after d5 transitions to d_ident, which
  accepts `Ident` only (the keyword match no longer applies). This is
  unambiguous: `alt_accepts = []`.

### 4.6. Hopcroft Minimization

States d1 through d4 all have `accept = Some(Ident)`, `alt_accepts = []`, and
similar transition structure. Some may be merged by minimization.

State d5 has `accept = Some(Fixed("error"))`, `alt_accepts = [(Fixed("error"),
0.0), (Ident, 9.0)]`. Because its partition key differs from d_ident (which has
`accept = Some(Ident)`, `alt_accepts = []`), d5 is never merged with any
unambiguous state.


## 5. Complexity Analysis

### 5.1. Unambiguous States: Zero Overhead

For unambiguous DFA states (0 or 1 accepting NFA states in the powerset),
`resolve_accept` returns `alt_accepts = Vec::new()`. This is a zero-length
`Vec` allocation (no heap allocation on most implementations). The `BTreeMap` in
`resolve_accept` contains at most 1 entry and is dropped immediately.

**Memory:** 0 bytes additional per unambiguous state (the `Vec` field is 3
machine words of inline storage: pointer, length, capacity).

**Time:** The `BTreeMap` operations for a single entry are effectively O(1).

### 5.2. Ambiguous States: Bounded Overhead

Ambiguous states arise only when a keyword's character sequence also matches a
character-class pattern (identifier, integer, etc.). In practice:

| Grammar property | Typical count |
|---|---|
| Keywords per grammar | 5-30 |
| Keywords overlapping identifiers | 5-30 (most keywords are identifier-shaped) |
| Alternatives per ambiguous state | 2 (keyword + ident) |
| DFA states per keyword | 1 (only the final character position is ambiguous) |

**Memory per ambiguous state:**

```
alt_accepts: Vec<(TokenKind, TropicalWeight)>
           = Vec<(enum(~32B), f64)>
           ~ 2 elements * 40 bytes = 80 bytes + 24 bytes Vec overhead
           ~ 104 bytes per ambiguous state
```

**Total additional memory:** O(k) where k is the number of keywords, typically
under 3 KB even for large grammars.

### 5.3. `resolve_accept` Time Complexity

Let a = number of accepting NFA states in the powerset set.

| Operation | Complexity |
|---|---|
| Collect into `BTreeMap` | O(a log a) |
| Sort alternatives by weight | O(a log a) |
| Total per DFA state | O(a log a) |

Since a is typically 1-2 (at most one keyword + one regex pattern), this is
effectively O(1) per DFA state.

### 5.4. Hopcroft Minimization Overhead

The extended partition key adds the `alt_accepts` comparison to the initial
partitioning step. This increases the number of initial partitions by at most k
(the number of ambiguous states with distinct alternative sets).

| Phase | Standard | Extended |
|---|---|---|
| Initial partitions | O(token_kinds) | O(token_kinds + ambiguous_variants) |
| Worklist iterations | O(n k log n) | O(n k log n) (unchanged) |
| Per-iteration work | O(1) compare | O(1) compare (alt_accepts in partition key is pre-computed) |

The worklist complexity is unchanged because the number of additional initial
partitions is bounded by the number of keywords, which is a grammar-level
constant. The refinement loop's dominant cost remains the inverse transition
map traversal.

### 5.5. Summary Table

| Metric | Unambiguous State | Ambiguous State |
|---|---|---|
| Additional memory | 0 bytes (empty Vec) | ~104 bytes |
| `resolve_accept` overhead | O(1) | O(a log a), a ~ 2 |
| Minimization overhead | 0 | O(1) per additional partition |
| Typical ambiguous states per grammar | 0 | 2-30 |
| Total overhead for 20-keyword grammar | -- | ~2 KB memory, ~microseconds |


## 6. Source References

All file paths are relative to the `prattail/src/` directory within the
workspace root.

| Component | File | Lines |
|---|---|---|
| `DfaState` struct with `alt_accepts` field | `automata/mod.rs` | 197-237 |
| `DfaState::is_ambiguous()` | `automata/mod.rs` | 234-236 |
| `Dfa::has_ambiguous_accepts()` | `automata/mod.rs` | 278-280 |
| `Dfa::ambiguous_states()` | `automata/mod.rs` | 286-294 |
| `TokenKind::priority()` | `automata/mod.rs` | 62-74 |
| `TropicalWeight::from_priority()` | `automata/semiring.rs` | 101-103 |
| `ResolvedAccept` struct | `automata/subset.rs` | 152-160 |
| `resolve_accept()` function | `automata/subset.rs` | 167-210 |
| `subset_construction()` (uses `resolve_accept`) | `automata/subset.rs` | 48-145 |
| Hopcroft `PartitionKey` with `alt_accepts` | `automata/minimize.rs` | 87-91 |
| Initial partition grouping (Step 2) | `automata/minimize.rs` | 78-117 |
| Minimized state construction (Step 5) | `automata/minimize.rs` | 255-306 |
| BFS canonical reordering (propagates `alt_accepts`) | `automata/minimize.rs` | 326-386 |
| `NfaState::accepting()` (weight from priority) | `automata/mod.rs` | 137-146 |
| `build_keyword_trie()` (NFA keyword construction) | `automata/nfa.rs` | 246-333 |
| Test: `test_multi_accept_keyword_ident` | `automata/subset.rs` | 301-355 |
| Test: `test_minimize_preserves_multi_accept` | `automata/minimize.rs` | 537-595 |
| Test: `test_minimize_does_not_merge_ambiguous_with_unambiguous` | `automata/minimize.rs` | 597-652 |


## 7. Invariants and Guarantees

The following invariants are maintained by the implementation and verified by
the test suite:

1. **Primary accept unchanged.** `DfaState.accept` always equals the
   highest-priority (lowest-weight) token kind, identical to the standard
   single-accept algorithm.

2. **Alt-accepts sorted.** `alt_accepts` is always sorted by tropical weight in
   ascending order (best first). `alt_accepts[0]` is always the primary winner.

3. **Empty when unambiguous.** `alt_accepts.is_empty()` if and only if the DFA
   state has 0 or 1 distinct accepting `TokenKind` values.

4. **Preserved through minimization.** `minimize_dfa` never merges states with
   different `alt_accepts` vectors.

5. **Preserved through canonicalization.** `canonicalize_state_order` copies
   `alt_accepts` verbatim to the reordered states.

6. **Idempotent.** Applying `minimize_dfa` or `canonicalize_state_order` a
   second time produces an identical DFA.
