# PathMap trie integration contract

**Status:** current cross-repository engineering contract, re-derived 2026-08-04

**MeTTaIL baseline:** `51d84ae3`

**F1r3node baseline:** `d68d8b9c`
**Audience:** maintainers changing Rholang path-map syntax, lowering, codecs, matching, or zipper operations

This document replaces the pre-integration transfer checklist that described `EPathMap` as a
`Vec<Par>`, used the retired `0xFF` key separator, and assumed one `PathMap<Par>` mode. Those claims
are historical and must not be used to design new code. The current contract is a homogeneous,
prefix-compressed trie from construction through serialization and node execution.

---

## 1. Notation

| Symbol or term | Meaning |
|---|---|
| **AST** | abstract syntax tree |
| **PDA** | pushdown automaton: finite control plus explicit heap stacks |
| **EPM1** | EPathMap format, version 1; the canonical homogeneous trie snapshot |
| **ACTree03** | PathMap's compact arena encoding used as EPM1 topology |
| **set mode** | value-free path membership stored as `PathMap<()>` |
| **map mode** | path-to-value association stored as `PathMap<Par>` |
| **neutral empty** | `{| |}` before an insertion has selected set or map mode |
| **canonical path** | the capless, injective, prefix-free byte encoding of one Rholang `Par` key |
| **projection** | materializing every member outside the trie, such as a `Vec<Par>` entry list |

The word *map* is overloaded in ordinary prose. Here **path map** means the PathMap trie. An
ordinary hash map is named explicitly and is never the target `EPathMap` representation.

---

## 2. Representation law

The node admits exactly three storage states:

```text
EPathMapRepr<Par> = Empty | Set(PathMap<()>) | Map(PathMap<Par>)
```

| Rholang surface | Mode | Stored key | Stored value |
|---|---|---|---|
| `{| |}` | neutral empty | none | none |
| `{| a, b, c |}` | set | `encode_trie_path(member)` | unit `()` |
| `{| k1: v1, k2: v2 |}` | map | `encode_trie_path(key)` | associated `Par` |

![Figure 1 — neutral empty specializes to one homogeneous PathMap mode](../../languages/figures/rholang-epathmap-modes.svg)

*Figure 1. The first insertion selects the trie specialization. A value cannot mix set-only and
key/value membership. Source:
[rholang-epathmap-modes.puml](../../languages/figures/rholang-epathmap-modes.puml).*

This law has four direct consequences:

1. Set mode does not retain a duplicate `Par` in each value slot. The canonical bytes are the
   member.
2. Map mode uses PathMap's value slot for the associated `Par`; it is not an `EMap` and is not a
   list of pairs.
3. Algebra, prefix queries, zippers, equality, hashing, and ordering operate on trie topology and
   values directly.
4. Mixed set/map membership is a typed refusal. It is never normalized into an option-valued map.

### 2.1 The empty edge case

`{| |}` cannot reveal an intended specialization at parse time. It therefore remains
`EPathMapRepr::Empty` until the first operation that requires a mode:

- a membership insertion selects `PathMap<()>`;
- a key/value insertion selects `PathMap<Par>`;
- an operation with one typed and one neutral operand inherits the typed operand's mode;
- an operation whose two neutral operands require a result mode refuses rather than guessing.

Removing the final entry may return the value to neutral empty only when no explicit value-free
topology remains. Code must query `mode()` instead of inferring mode from `len() == 0`.

---

## 3. The two repository layers

### 3.1 MeTTaIL syntax carrier

`mettail_runtime::PathMapLit<K,V>` preserves unresolved source keys and values while generated
binding, substitution, normalization, display, and semantic-hash PDAs operate on the Rholang AST.
It has the same `Empty | Set | Map` mode law. Its internal deterministic source collection is not
an `EPathMap`: canonical target bytes cannot be computed until a `Proc` is lowered with its bound
environment to `Par`.

The target boundary is `rholang-runtime/src/rholang_ast.rs:1890-1919,2372-2395,3421-3437`.
The iterative lowerer:

1. schedules one child per set member or two children per map entry;
2. lowers every child through the same explicit PDA;
3. calls `EPathMap::new` or `EPathMap::new_map` exactly once;
4. leaves the completed node value in F1r3node's homogeneous PathMap storage.

The transient PDA value stack is construction state, not an EPathMap projection. In particular,
no already-built target trie is converted back to a `Vec<Par>` during lowering.

### 3.2 F1r3node trie carrier

At F1r3node baseline `d68d8b9c`:

| Concern | Authoritative source |
|---|---|
| mode and EPM1 envelope | `models/src/rust/epathmap_trie_codec.rs:36-112` |
| `EntryTrie` storage and caches | `models/src/rust/rhoapi_ext.rs:69-105` |
| public `EPathMap` wrapper | `models/src/rust/rhoapi_ext.rs:2125-2513` |
| set/map aliases and canonical keys | `models/src/rust/pathmap_integration.rs:1-40` |
| protobuf schema record | `models/src/main/protobuf/RhoTypes.proto:321-364` |
| protobuf PDA | `models/src/rust/rholang/protobuf_encoder.rs` and `protobuf_decoder.rs` |
| bincode PDA | `models/src/rust/rholang/bincode_encoder.rs` and `bincode_decoder.rs` |

`EntryTrie` is a metadata-bearing owner around one PathMap root. It is not a shadow trie: the
`repr` field is the entry store. Its maintained folds make `len`, entry stability,
`locally_free` union, and `connective_used` queries constant-time without decoding all keys.

---

## 4. Canonical key encoding

The retired design joined S-expression segments with `0xFF`. The current key is
`canonical_path::encode_trie_path(par)`.

The codec has two top-level shapes:

- a split-eligible, ground `EList` contributes one prefix-free segment per element followed by the
  split terminator `0x00`;
- every other `Par` contributes one bare segment, using the total `0x0F` escape arm when structural
  ground encoding does not apply.

The split/bare cursor discriminator is necessary because the bare element `1` and singleton list
`[1]` share the same element segment but have distinct complete keys. Zipper cursors therefore
carry `Split`, `Bare`, or unresolved `Prefix` state; code must use the shared cursor-to-key helper
rather than concatenate bytes locally.

The codec obligations are:

```math
\operatorname{decode}(\operatorname{encode}(p)) = p
```

```math
p \ne q \Longrightarrow \operatorname{encode}(p) \ne \operatorname{encode}(q)
```

and no artificial traversal-depth limit may qualify either statement.

---

## 5. Trie-native serialization

New protobuf writers emit only field 9, `trie_snapshot`. Fields 1 and 8 are decoder-only legacy
inputs. Both protobuf and bincode carry EPM1, whose payload consists of:

1. magic and version;
2. homogeneous mode;
3. PathMap's prefix-compressed ACTree03 topology;
4. a value count and, in map mode, the associated `Par` values in topology ordinal order.

EPM1 is not an entry-list encoding. Set mode contains no `Par` value table. Map values are streamed
by the generated protobuf PDA from a PathMap zipper; they are not first gathered into a vector.
Bincode writes one canonical EPM1 byte slice and its stack-safe reader reconstructs the
homogeneous trie.

### 5.1 Why `trie_snapshot` exists

`trie_snapshot` is a lazy `Arc<OnceLock<Vec<u8>>>` serialization memo:

- the first request costs $`\Theta(t + v)`$ for trie topology size $`t`$ and encoded map-value size
  $`v`$;
- warm requests return the cached slice without rebuilding it;
- clones share a cold or warm memo until one clone mutates;
- mutation replaces both the snapshot and layout cells only on the mutated value.

Lookup, equality, hashing, ordering, algebra, and zipper navigation do not force this cache. The
memo therefore amortizes repeated wire writes without turning serialization bytes into the data
model. The former global intern store and its `contains_par` memo were deleted; direct PathMap
lookup is the membership mechanism.

---

## 6. Stack-safe traversal contract

All user-depth recursion at the integration boundary uses an explicit PDA. This includes generated
clone, drop, comparison, equality, hashing, normalization, substitution, matching, display,
protobuf, and bincode families, plus handwritten reducer and spatial-matcher machines.

**Algorithm 1 (Trie-aware post-order traversal).** Schedule trie members in the reverse of canonical
PathMap order so a last-in/first-out work stack evaluates them in forward order.

```pseudocode
TRAVERSE_EPATHMAP(root)
    push VISIT(root) on work
    while work is not empty
        instruction <- pop work
        if instruction is VISIT(EPathMap set)
            stream raw PathMap<()> keys in reverse trie order
            push one DECODE_SET_KEY instruction per key
        else if instruction is VISIT(EPathMap map)
            stream borrowed PathMap<Par> key/value pairs in reverse trie order
            push value and key work without cloning either collection
        else
            execute the ordinary generated node instruction
    return the single completed result
```

Reverse streaming is important: allocating a forward `Vec<&Par>` merely to reverse its order
would restore a width-proportional projection. Owned zipper iterators are used when destructive
machines must move entries out of the trie. Neither strategy changes PathMap itself.

Completion requires all of the following to stay absent:

- `RUST_MIN_STACK` increases;
- the `stacker` crate;
- traversal-depth caps;
- recursive fallback for deep inputs;
- conversion of a completed EPathMap to an entry vector.

---

## 7. Algebra, lattice, and zipper rules

Set operations delegate to the lawful `PathMap<()>` unit-value algebra. Map operations apply
PathMap topology operations and resolve overlapping `Par` values through the operation's declared
semantics. A cross-mode operation refuses before mutation.

Prefix queries work on the branch at the zipper focus, while exact-key operations use the cursor's
split/bare discriminator. Subtrie iterators return keys relative to their focus; callers that emit
an absolute EPathMap must prepend the focus exactly once.

The following are architectural defects, even if a focused example appears to work:

- rebuilding algebra with `Vec`, `HashSet`, `HashMap`, or sorted pairs;
- decoding every set key before an exact membership query;
- comparing cached EPM1 snapshots instead of trie topology and values;
- implementing a second path codec in MeTTaIL;
- adding a PathMap fork to work around an integration bug.

`runtime/src/pathmap_codec.rs` in MeTTaIL exports the old escaped-`0xFF` segment helper and has no
production call site at baseline `51d84ae3`. It is not the F1r3node canonical codec and must not be
used for EPathMap lowering or conformance. Its public-API retirement should be handled as an
explicit compatibility cleanup, not silently folded into a codec change.

---

## 8. Verification obligations

Every generated PDA must be checked against the retained recursive test oracle on shallow values,
then exercised beyond native-stack-safe recursive depth. Formal evidence covers the generic
machine invariant, mode transitions and refusal, set/map algebra laws, and the EPM1 envelope/value
table. Executable PathMap parsing remains an explicit trusted boundary.

The cross-repository gate must cover:

1. neutral empty, set, and map lowering;
2. mixed-membership refusal;
3. exact-key lookup and prefix queries;
4. algebra and zipper operations in both specializations;
5. protobuf and bincode byte round trips;
6. deep keys, deep map values, and wide tries;
7. generated-PDA versus recursive-oracle equivalence;
8. deterministic bytes, hashes, ordering, and replay-visible results.

The scientific measurements and proofs are maintained in F1r3node's living
`docs/design/stack-safety/stack-safety-report-2026-07-29.md`,
`docs/design/pathmap/pathmap-report-2026-08-03.md`, and
`docs/consensus/consensus-change-register.md`. This handoff states the contract; it does not copy
their evolving evidence tables.

---

## 9. References

- [Rholang language reference](../../languages/rholang.md) — the MeTTaIL syntax, lowering, and
  execution boundary.
- [Lookahead PathMap design history](lookahead-traces-as-a-pathmap.md) — a superseded proposal whose
  current-state reconciliation explains which integration gaps closed.
- F1r3node sources and living reports at sibling checkout
  `/home/dylon/Workspace/f1r3fly.io/f1r3node-rust-mettail`, baseline `d68d8b9c`. These are outside
  this repository. (no DOI registered)
- The `pathmap` crate, version 0.2.2 with `arena_compact`, provides the radix trie, algebra, compact
  arena, and zipper APIs. (no DOI registered)
