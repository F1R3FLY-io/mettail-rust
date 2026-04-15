# CEK-9A: GLL Parsing via Graph-Structured Stack

## Intuition

GLL parsing generalizes the CEK continuation stack to a **graph-structured stack (GSS)** where multiple parse states share common continuations. This handles ALL ambiguity natively — instead of NFA try-all backtracking, GLL explores all alternatives simultaneously with structural sharing.

## Key Insight

The `im::Vector` CoW stack already provides structural sharing for consecutive checkpoints. Extending to allow **forking** (multiple stack tops sharing a common suffix) turns the checkpoint infrastructure into a full GLL parser.

## GSS Architecture

```
    [InfixRHS, pos=3]──┐
                        │
    [RD_A_0, pos=2] ───┤──▶ [GroupClose, pos=1] ──▶ [root, pos=0]
                        │
    [RD_B_0, pos=2] ───┘
```

Three frontier nodes at positions 2-3 share a common suffix `[GroupClose, root]`. This is the GSS's key advantage: instead of duplicating the entire stack for each alternative, only the divergent prefix is separate.

## Algorithm

1. Start with a single root node in the GSS
2. When prefix dispatch is ambiguous (multiple rules match):
   - **Fork** the GSS: create one new frontier node per alternative
   - Each frontier node shares the current node as its continuation
3. Process all frontier nodes in parallel (round-robin or worklist)
4. When a frontier node completes parsing:
   - Merge its result into the packed parse forest (SPPF)
5. Use WFST weights to select the best parse from the SPPF

## Types

### GssNode
```rust
pub struct GssNode {
    pub pos: usize,           // Input position
    pub frame_tag: String,    // Frame variant name
}
```

### GraphStructuredStack
```rust
pub struct GraphStructuredStack {
    nodes: Vec<GssNode>,
    edges: HashMap<GssNodeId, Vec<GssEdge>>,
    frontier: Vec<GssNodeId>,
    node_index: HashMap<GssNode, GssNodeId>,
}
```

### SPPF (Shared Packed Parse Forest)
```rust
pub enum SppfNode {
    Terminal { pos, text },
    Interior { label, start, end, children },
    Packed { alternatives },  // Ambiguous derivation
}
```

## Zero-Overhead Fallback

For unambiguous grammars, the GSS degenerates to a linear stack (each node has exactly one edge). The overhead is zero because:
1. No forking occurs → single frontier node
2. No packed nodes in SPPF → standard parse tree
3. GssNodeId lookup is O(1) via HashMap

## Feature Gate

`gll-parsing = ["reactive-cek"]`

## References

- Scott, E. & Johnstone, A. (2010). *GLL parsing.* ENTCS.
- Tomita, M. (1986). *Efficient parsing for natural language.* Kluwer.
