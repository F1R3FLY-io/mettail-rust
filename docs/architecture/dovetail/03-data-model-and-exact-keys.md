# Data Model and Exact Keys

Dovetail's data model is designed around exact identity. A finite hash is never
the semantic identity of a term or derivation.

## E-Graph Model

An e-node is:

`n = op(children)`

where `op` is a payload-generic label and `children` is an ordered vector of
e-class identifiers.

An e-class is a set of equivalent e-nodes:

`q = { n₁, n₂, … }`

The e-graph maintains:

| Structure | Purpose |
|---|---|
| union-find | canonical representative of each e-class |
| class table | live e-class to e-node vectors and parent links |
| memo table | exact structural hashconsing of canonical e-nodes |
| pending merges | congruence worklist |
| node budget | hard cap for fresh e-node insertion |

## Exact Content Key

`ContentKey` is an owned byte stream. Equality and ordering are bytewise.

For e-node identity, Dovetail uses length framing:

`key(op(c₁, …, cₙ)) = bytes(op) · frame(c₁) · … · frame(cₙ)`

Length framing prevents concatenation aliasing:

`frame("ab") · frame("c") ≠ frame("a") · frame("bc")`

For derivation ordering, Dovetail uses ordered framing:

`orderedFrame(b₀…bₙ) = 0x01 b₀ · … · 0x01 bₙ · 0x00`

The ordered frame is prefix-free and lexicographic-order preserving. That is
why parent derivation keys can use child keys as tiebreaking material without
inverting child order.

## SemanticHash Contract

`SemanticHash` is an unsafe trait because implementors promise:

`write_content(x) = write_content(y) ⇔ x ≈ y`

and:

`x = y ⇒ hash(x) = hash(y) ∧ write_content(x) = write_content(y)`

Composite values must frame parts. Failing to frame parts can make structurally
different values write the same byte stream.

## Rebuild Invariants

After `merge` and `rebuild`, these invariants hold:

| Invariant | Meaning |
|---|---|
| canonical children | every live e-node child points through `find` |
| exact memo | no two memo entries represent the same canonical e-node |
| parent links | every parent edge is registered on each canonical child |
| class-local dedup | duplicate canonical e-nodes inside a class are collapsed |
| live node count | `node_count` equals the number of live exact e-nodes |

Literate pseudocode:

```text
To rebuild exact indexes:
  Snapshot union-find representatives.
  For each live class, canonicalize all node children.
  Keep only the first exact canonical copy of each node.
  Clear parent links.
  Rebuild memo from canonical nodes.
  Rebuild parent links from each canonical child to its parent node.
  Recompute live node count from exact memo insertions.
```

## Runtime-Facing Reports

Reports are Dovetail's proof-preserving handoff artifacts. They are not
human-facing logs and they are not Ascent-style fact bags. The dedicated
contract is documented in
[Runtime-Facing Reports](10-runtime-facing-reports.md).

`report_from_extraction` converts checked derivations into:

| Field | Meaning |
|---|---|
| `roots` | exact root keys in extractor order |
| `root_ordinals` | root positions in the term table |
| `terms` | unique derivation nodes by exact key |
| `derivation_edges` | parent-child edges preserving multiplicity and order |
| `completeness` | terminal extraction completeness |

Reports preserve exact identity while giving adapters stable ordinals for table
layout. Ordinals are presentation identifiers; exact keys remain semantic
identifiers.
