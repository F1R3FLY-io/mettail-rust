# Lookahead traces as a PathMap

**Status:** implemented integration report, re-derived 2026-08-04

**MeTTaIL baseline:** `51d84ae3`

**F1r3node baseline:** `d68d8b9c`
**Normative proposal:** F1r3fly Improvement Process Submission `2026-01-08-Lookahead.md`

This report replaces the earlier proposal preserved under this filename. That proposal described a
flat set of digest lists, copied trace vectors, list-backed EPathMaps, a missing EPathMap matcher
arm, and unavailable `last`/lowering operations. All of those implementation premises are now
obsolete. This page records the current process-trace, search, and PathMap delivery architecture.

---

## 1. Notation

| Symbol or term | Meaning |
|---|---|
| **FIPS** | F1r3fly Improvement Process Submissions; here, the lookahead proposal |
| **BFS** | breadth-first search |
| **COMM** | one committed communication between matching RSpace data and continuation |
| **PDA** | pushdown automaton with explicit heap stacks |
| **EPM1** | EPathMap format, version 1; F1r3node's canonical trie snapshot |
| **EPathMap** | homogeneous `Empty | Set(PathMap<()>) | Map(PathMap<Par>)` Rholang path trie |
| **trace** | the complete root-to-leaf process/configuration sequence for one branch |
| **step** | one selected COMM and the configuration that exists after it |
| **leaf** | a quiescent, truncated, or aborted branch result |
| $`E(S)`$ | the enabled rendezvous set in store configuration $`S`$ |
| $`D`$ | maximum explored COMM depth |
| $`E`$, $`L`$ | the explored edge count and delivered leaf count |

---

## 2. Required semantic shape

For `x!(P)[n]`, the proposal requires every result to retain the trace, not merely a digest that
names it. The current implementation publishes:

```text
process-trace   ::= [input, saturated-initial, state1, ..., terminal]
success-entry   ::= process-trace
truncated-entry ::= process-trace ++ [(handle, frontier)]
failure-entry   ::= process-prefix ++ [[code, message]]
```

`handle` is a 32-byte digest used to resume host-retained state. It names the complete path but
does not replace a process node. `frontier` is $`|E(S)|`$ at the truncation point. Failure appends
the two-element error list required by the proposal and does not pretend that a failed step fired.

Three collections are published:

| Collection | Branch condition | Terminal information |
|---|---|---|
| `success` | $`E(S) = \varnothing`$ | reified quiescent configuration |
| `truncated` | the requested depth ended and $`E(S) \ne \varnothing`$ | resumable handle and frontier size |
| `failure` | reduction or resource refusal | stable error code and bounded message |

Truncation is neither success nor failure. Keeping a third collection makes that distinction
machine-readable and allows beam search to resume a selected subset without reconstructing random
state from a `Par`.

![Figure 1 — current trace path from shared in-memory history to set-mode EPathMap](figures/lookahead-trace-shape.svg)

*Figure 1. Every delivered member is a complete process path. `PathMap<()>` owns set membership,
canonical order, deduplication, prefix compression, and EPM1 serialization. Source:
[lookahead-trace-shape.puml](figures/lookahead-trace-shape.puml).*

---

## 3. Persistent and stack-safe in-memory traces

`rholang-runtime/src/speculation.rs:572-759` defines `ReductionTrace` as:

- an `Arc<[Par]>` root containing the input and saturated initial configuration;
- an optional `Arc<TraceLink>` tail;
- a COMM count;
- a rolling content digest.

Each `TraceLink` points to its parent and owns the structured rendezvous name plus the reified
post-COMM configuration. Extending a branch allocates one link and increments at most one shared
reference count, so extension is $`\Theta(1)`$ in trace depth. Sibling branches share their prefix.

`processes()` and `rendezvous_names()` materialize root-to-leaf order iteratively. `Drop` repeatedly
unwraps the unique suffix and stops at the first shared prefix, avoiding recursive `Arc` teardown.
`Clone` is an `Arc` clone rather than a copy of every ancestor.

![Figure 2 — ReductionTrace shares branch prefixes and uses iterative materialization and teardown](figures/lookahead-trace-representation.svg)

*Figure 2. The implemented persistent trace changes per-edge copying into constant-time extension;
materialization occurs once for each delivered leaf. Source:
[lookahead-trace-representation.puml](figures/lookahead-trace-representation.puml).*

**Algorithm 1 (Extend and materialize a persistent trace).** Store each result behind one immutable
parent link, then fill the final output from leaf to root without recursion.

```pseudocode
EXTEND(trace, rendezvous, result)
    digest <- hash(trace.digest, canonical_protobuf(result))
    tail <- Arc(TraceLink(parent = trace.tail, rendezvous, result))
    return ReductionTrace(trace.root, tail, trace.steps + 1, digest)

MATERIALIZE(trace)
    output <- fixed array of trace.root.length + trace.steps
    copy root processes into the prefix of output
    cursor <- trace.tail
    index <- output.length
    while cursor exists
        index <- index - 1
        output[index] <- clone(cursor.result)
        cursor <- cursor.parent
    return output
```

The output construction costs $`\Theta(d)`$ at a leaf of depth $`d`$, which is unavoidable because
the published path contains those $`d`$ nodes. Across a search, trace-structure work is
$`\Theta(E)`$ and final materialization is $`\Theta(L \cdot D)`$ in the worst case. Native-stack
use remains constant in $`D`$.

---

## 4. Search-state resource behavior

`rholang-runtime/src/speculation/search.rs:880-1272` runs a level-stratified search with three
selectable semantics:

| Mode | State-space interpretation |
|---|---|
| `IndependenceReduced` | graph search plus sleep-set partial-order reduction |
| `DistinctConfigurations` | graph search; merge equal configurations |
| `EveryTrace` | tree search; retain every choice sequence |

The visited key is a 32-byte content digest rather than a retained vector of formatted map entries.
A singleton conflict class moves its `HotStoreState` into the sandbox and needs no full-state clone.
A branching node retains one parent snapshot; later siblings clone only while another sibling still
needs that parent, and the final sibling consumes it by move.

The remaining heap slope is semantic state, not recursive-stack growth:

- the frontier must retain one store state per live branch;
- a true conflict class needs enough parent copies to evaluate its alternative firings;
- delivered PathMap keys must contain the complete process paths requested by the interface.

Those allocations can exhaust a memory budget for an enormous state space, but they cannot cause a
native stack overflow. No `RUST_MIN_STACK`, `stacker`, or traversal-depth cap is part of the search.
A persistent `HotStoreState` could reduce branch-copy cost further, but it is a separate RSpace data
model decision rather than an EPathMap correction.

### 4.1 Metering is the termination bound

The sandbox is funded from the host deploy's remaining budget. One budget unit corresponds to one
committed COMM, independent of the diagnostic `Cost.value` supplied to `reserve_comm`. Charging
back $`k`$ speculative COMMs therefore requires $`k`$ calls to the host's ordinary reserve point.

Unbounded lookahead owns no private node cap or traversal-depth cap. It terminates by exhausting a
finite host budget or by reaching quiescence, using the same accounting authority as ordinary node
execution.

---

## 5. Trie-native delivery

`rholang-runtime/src/speculation/delivery.rs:1580-1715` constructs all three results as set-mode
EPathMaps. `EPathMap::from_set_iter` encodes each completed trace entry directly into
`PathMap<()>`; the target retains neither a `Vec<Par>` member list nor a redundant value copy.

The three temporary vectors inside `deliver` provide failure-atomic construction: every success and
truncated leaf is reified and checked before any result is returned. They are input staging for a
new trie, not a projection of an existing EPathMap, and disappear after construction. The completed
collections retain only PathMap topology and metadata.

Set mode is important here:

- output branch order is not observable;
- duplicate process paths collapse by canonical key;
- common process prefixes share trie topology;
- both ground and non-ground `Par` paths are total through the canonical codec's escape arm;
- protobuf and bincode serialize the same EPM1 trie image.

Producer-side configuration canonicalization is still required. PathMap preserves the bytes of a
member; it cannot decide that two differently ordered process representations mean the same store.
`reify` and `resting_on` therefore sort store-owned collections by content-derived keys before
creating a process path.

![Figure 3 — deterministic delivery into three homogeneous PathMap sets](figures/lookahead-groundness-and-ordering.svg)

*Figure 3. Reification canonicalizes each path member, and PathMap canonicalizes the unordered
collection of members. Both stages are required for scheduler-invariant output. Source:
[lookahead-groundness-and-ordering.puml](figures/lookahead-groundness-and-ordering.puml).*

---

## 6. Query and matching accessibility

The integration gaps named in the superseded proposal are closed at F1r3node baseline `d68d8b9c`:

| Former gap | Current disposition |
|---|---|
| MeTTaIL `lower_pathmap` | iterative lowering constructs set/map `EPathMap` directly |
| zipper/pathmap method routing | routed against native `EPathmapBody` and `EZipperBody` carriers |
| `last` | reducer method is present and shares `nth`'s failure behavior |
| `EPathmapBody` spatial matching | explicit set/map PDA arm, including retry and remainder behavior |
| list-backed wire format | replaced by homogeneous EPM1 trie serialization |

Programs can therefore use exact membership, prefix queries, zipper navigation, algebra, and
spatial matching without flattening a trace collection. Exact method names and refusal behavior are
pinned in `rholang-runtime/tests/rho_rholang_conformance.rs` and the target reducer suites.

---

## 7. Determinism and verification

The following distinctions are load-bearing:

1. A trace digest is order-sensitive and names one process path.
2. A content fingerprint is insensitive to store enumeration order and identifies a configuration.
3. An EPathMap is an unordered set of complete canonical paths.
4. Randomness and store indices are host state; a reified process is inspectable but is not a
   substitute for a resumable handle.

The current verification surface includes:

- `rholang-runtime/tests/x8_publication_is_scheduler_invariant.rs` for scheduler-width invariance;
- `rholang-runtime/tests/s2_speculative_branching.rs` for three-outcome branching and PathMap
  delivery;
- `rholang-runtime/tests/rho_rholang_conformance.rs` for lowering and native method parity;
- `rholang-runtime/src/speculation/delivery.rs` unit cells for construction-order independence,
  trace-terminal integrity, and set-mode EPathMap output;
- F1r3node's PathMap, protobuf, bincode, matcher, and stack-safety suites for the target carrier.

The two cross-repository living reports remain authoritative for changing evidence:

- `f1r3node-rust-mettail/docs/design/stack-safety/stack-safety-report-2026-07-29.md`;
- `f1r3node-rust-mettail/docs/consensus/consensus-change-register.md`.

This report must be updated if a change moves any of the following: delivered entry shape, trace
mode, canonicalization order, PathMap mode, EPM1 bytes, host charging, or resumable-handle identity.

---

## 8. Residual engineering questions

These are not missing EPathMap integration:

- whether the normative proposal adopts the implemented third `truncated` collection;
- which trace mode should be the user-facing default for each guest;
- whether RSpace eventually adopts a persistent `HotStoreState` representation;
- whether result construction should replace its three failure-atomic staging vectors with a
  transactional trie builder after profiling shows a material benefit.

None permits replacing PathMap with a list, set, ordinary hash map, or pair vector. Any future
optimization must preserve the set-mode EPathMap value and the deterministic process-path bytes.

---

## 9. References

- [PathMap integration contract](SPEC-pathmap-trie-transfer.md) — current homogeneous carrier,
  canonical codec, serialization, and stack-safe traversal rules.
- [Rholang language reference](../../languages/rholang.md) — generated syntax and lowering boundary.
- The lookahead FIPS, `approved/2026-01-08-Lookahead/2026-01-08-Lookahead.md` in the sibling FIPS
  repository. It is outside this repository. (no DOI registered)
- F1r3node source and living reports in sibling checkout
  `/home/dylon/Workspace/f1r3fly.io/f1r3node-rust-mettail`, baseline `d68d8b9c`. (no DOI registered)
