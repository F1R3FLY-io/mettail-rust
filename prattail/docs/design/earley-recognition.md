# CEK-9B: Earley Recognition via CEK Chart

## Intuition

Build an Earley chart from CEK traces — providing O(n³) recognition for ambiguous grammars vs exponential NFA try-all. Does NOT replace Pratt for unambiguous cases — used as fallback for highly ambiguous regions.

## CEK → Earley Mapping

| CEK Concept | Earley Concept |
|------------|---------------|
| `(pos, state, stack_depth)` | Earley item `(rule, dot_pos, origin)` |
| `CekTraceEntry::Drive` | PREDICT operation |
| `CekTraceEntry::Value` | SCAN operation |
| `CekTraceEntry::Pop` | COMPLETE operation |

## Algorithm

### Chart Population from CEK Trace

1. For each `CekTraceEntry`:
   - **Drive at pos**: PREDICT all rules for the category at position pos
   - **Value at pos**: SCAN the token at pos, advancing items expecting it
   - **Pop at pos**: COMPLETE items whose dot is at the end of their rule

### SPPF Extraction (Scott, 2008)

From a completed chart, extract a Shared Packed Parse Forest:
1. Start from completed items at position n with origin 0
2. Recursively build tree nodes for each item
3. Packed nodes represent ambiguous derivations

## Leo Optimization (CEK-9C)

### Problem

Right-recursive grammars produce O(n²) Earley items due to chains of right-recursive completions.

### Solution

Leo (1991) detects **deterministic reduction chains** — sequences where each completion triggers exactly one further completion. These chains are compressed into a single **Leo item**.

### CEK Connection

In CEK terms, Leo optimization IS continuation compression (CEK-2) applied to the Earley chart. The `tail_wrap` mechanism handles the same pattern at the parser level.

### Detection

A rule is Leo-eligible if:
1. It is right-recursive (last syntax item is same-category NT)
2. At the completion point, exactly one item expects this category
3. That item would itself complete after advancing

### Complexity

| Grammar Class | Standard Earley | With Leo |
|--------------|----------------|----------|
| Unambiguous | O(n²) | O(n) |
| Right-recursive | O(n²) | O(n) |
| Ambiguous | O(n³) | O(n³) |

## Feature Gate

`earley-recognition = ["reactive-cek"]`

## References

- Earley, J. (1970). *An efficient context-free parsing algorithm.* CACM.
- Leo, J. (1991). *A general context-free parsing algorithm running in linear time on every LR(k) grammar.* TCS.
- Scott, E. (2008). *SPPF-style parsing from Earley recognisers.* ENTCS.
