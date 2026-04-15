# CEK-1: Environment Trimming (Dead Capture Elimination)

## Intuition

When the trampoline parser splits an RD rule into segments at same-category nonterminal boundaries, each segment's frame stores **all** previously captured values. But many of these captures are never referenced by subsequent segments or the final constructor. They are "dead" — wasting space in the frame variant.

For example, consider a rule with 4 segments where segment 1 captures `x`, segment 2 captures `y`, segment 3 uses only `y`, and the constructor uses both `x` and `y`. The frame at segment 2 would carry both `x` and `y`, but the frame at segment 3 only needs `y` (since `x` is not used by any segment after 3).

## Theoretical Basis

This is a standard **backward liveness analysis** over a lattice of capture-name sets:

```
⊥ = ∅  (no captures live)
⊤ = all_captures  (all captures live)
join = ∪  (union)
```

**Transfer function** for segment i:
```
live_in[i] = used_in[i+1] ∪ live_in[i+1]
```

where `used_in[i]` is the set of capture names referenced by segment i's inline items.

**Initialization:**
```
live_in[n-1] = constructor_capture_names(rule)
```

The analysis runs in a single backward pass (no fixed-point iteration needed because the segment graph is a chain — no loops).

## Algorithm

```
function compute_live_captures(segments, constructor_names):
    n ← |segments|
    live_at ← array of n empty sets
    live_at[n-1] ← constructor_names

    for i from n-2 down to 0:
        live_at[i] ← live_at[i+1]
        for each item in segments[i+1].inline_items:
            live_at[i] ← live_at[i] ∪ referenced_names(item)

    for i from 0 to n-1:
        segments[i].accumulated_captures ←
            filter(segments[i].accumulated_captures, λ cap. name(cap) ∈ live_at[i])
```

**Complexity:** O(n × m) where n = number of segments and m = max captures per segment.

## Connection to Register Automata

Each capture can be modeled as a **register** in a register automaton (Kaminski & Francez, 1994). The liveness analysis corresponds to `RegisterAutomaton::minimize()`, which eliminates dead registers. The lattice dataflow over capture-set lattice corresponds to the fixed-point in `lattice_theory.rs`.

## Implementation

### Files Modified

| File | Change |
|------|--------|
| `trampoline.rs` | `compute_live_captures()`, `trim_dead_captures()`, `capture_name()`, `collect_referenced_names()`, `constructor_capture_names()` |
| `cost_benefit.rs` | `Optimization::EnvironmentTrimming`, gate `environment_trimming` |
| `lint.rs` | `lint_cek01_dead_capture_in_frame()` |

### Optimization Gate

- **Code:** `CEK01`
- **Name:** `EnvironmentTrimming`
- **Speedup:** 0.15 (modest — smaller frames reduce memory traffic)
- **Cost:** 0.05 (very low — static analysis, single backward pass)
- **Applicability:** Always applicable

### Lint

- **Code:** `CEK01`
- **Name:** `dead-capture-in-frame`
- **Severity:** Note
- **Message:** Reports frame variants carrying dead captures
- **Hint:** Enable CEK01:EnvironmentTrimming

## Example

Given rule `Let`:
```
Let . x:Ident "=" body:Expr "in" result:Expr → Expr
```

Segments:
```
Segment 0: inline=[Ident(x), "="], NT=Expr(body), captures=[]
Segment 1: inline=["in"],           NT=Expr(result), captures=[x, body]
Segment 2: inline=[],               NT=None,         captures=[x, body, result]
```

Constructor uses: `x`, `body`, `result` (all three).

Liveness analysis:
```
live_at[2] = {x, body, result}    (constructor)
live_at[1] = {x, body, result}    (segment 2 uses nothing inline, but live_at[2] propagates)
live_at[0] = {x, body, result}    (segment 1 uses nothing extra)
```

In this case, no captures are dead. But consider a different rule:

```
Debug . x:Ident ";" y:Expr ";" z:Expr → Expr::Debug(z)
```

Constructor uses only `z`. Liveness:
```
live_at[2] = {z}
live_at[1] = {z}       (segment 2 adds no new inline refs)
live_at[0] = {z}       (segment 1 adds no new inline refs)
```

Frames **before** trimming: segment 0 carries `[]`, segment 1 carries `[x, y]`, segment 2 carries `[x, y, z]`.

Frames **after** trimming: segment 0 carries `[]`, segment 1 carries `[]`, segment 2 carries `[z]`.

Dead captures eliminated: `x` and `y` from segments 1 and 2.
