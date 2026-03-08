# N02: unbounded-channel

**Severity:** Warning
**Category:** analysis/concurrency
**Feature Gate:** `petri`

## Description

Detects places in the Petri net model of the grammar that have unbounded token
capacity. An unbounded place can accumulate an unlimited number of tokens,
representing a channel, buffer, or parser state that grows without bound. This
is a resource exhaustion risk: the parser may consume unbounded memory if the
corresponding grammar construct produces tokens faster than they are consumed.

The analysis constructs a Karp-Miller coverability tree from the Petri net and
examines each place for the presence of the omega (omega) marker, which indicates
that the place's token count can grow without bound.

### Karp-Miller coverability tree

The Karp-Miller algorithm builds a tree of reachable markings, using the omega
symbol to represent unbounded growth:

```
  Karp-Miller Tree Construction
  ═════════════════════════════

  Petri net:
    Places:      {p_in, p_buf, p_out}
    Transitions: {t_produce, t_consume}

    t_produce: p_in --> p_buf     (pre: {p_in:1}, post: {p_buf:1})
    t_consume: p_buf --> p_out    (pre: {p_buf:1}, post: {p_out:1})

  Initial marking: M_0 = (p_in: omega, p_buf: 0, p_out: 0)
  (omega tokens in p_in = unbounded input stream)

  Coverability tree:

                  (omega, 0, 0)
                      │
           t_produce  │
                      v
                  (omega, 1, 0)
                    /       \
       t_produce  /          \  t_consume
                 v            v
           (omega, 2, 0)  (omega, 0, 1)
               │              │
    acceleration│              │ t_produce
               v              v
        ┌──────────────┐  (omega, 1, 1)
        │(omega, omega,│      │
        │     0)       │      ...
        └──────────────┘
              ^
              │
       omega introduced: p_buf grows without bound
       because t_produce can fire indefinitely
       while t_consume is not forced to keep pace.

  Legend:
    omega = unbounded token count (can grow to infinity)
    (a, b, c) = marking of (p_in, p_buf, p_out)
    acceleration: when a new marking M' >= an ancestor M
      on the same path, any component where M'(p) > M(p)
      is replaced by omega.
```

The acceleration step is the key mechanism: when the tree explores a marking
that strictly dominates an ancestor marking on the same path (i.e., for some
place p, the new marking has more tokens than the ancestor), the dominated
component is replaced by omega. This indicates that the place can accumulate
unboundedly many tokens by repeating the firing sequence between the ancestor
and the descendant.

In the example above, `p_buf` receives an omega marker because `t_produce`
can fire repeatedly (consuming from the unbounded `p_in`) without `t_consume`
being forced to fire in lockstep. The result is that `p_buf` is flagged as
an unbounded place.

### Formal criterion

A place p is unbounded if there exists a node n in the Karp-Miller tree such
that n.marking(p) = omega. Equivalently:

  exists M in Cover(N) . M(p) = omega

where Cover(N) is the set of markings in the coverability tree of net N.

## Trigger Conditions

A warning is emitted **once per unbounded place** when **all** of the following
conditions hold:

1. The `petri` feature is enabled.
2. The pipeline's Petri net module (`petri.rs`) has been executed, producing a
   `PetriAnalysis`.
3. The result's `unbounded_places` vector is non-empty.

One diagnostic is emitted for each place name in `unbounded_places`.

The lint is silent when:
- The `petri` feature is not enabled.
- No `PetriAnalysis` is available (analysis was not run).
- The `unbounded_places` vector is empty (all places are bounded).

## Example

### Grammar

```
language! {
    name: StreamLang;
    primary: Stream;

    category Stream {
        Emit  = "emit" "(" Expr ")" ";" Stream;
        Drain = "drain" "(" Chan ")";
        Par   = Stream "|" Stream;
        Done  = "done";
    }

    category Expr {
        native_type: Integer;
        IntLit = <int>;
        Add    = Expr "+" Expr;
    }

    category Chan {
        ChanId = <ident>;
    }
}
```

The `Emit` rule produces values into a channel without any back-pressure
mechanism. If one branch of `Par` emits indefinitely while the other branch
drains at a finite rate, the channel buffer grows without bound.

### Output

```
warning[N02] (StreamLang): place `channel_in` has unbounded token capacity
  = hint: consider adding a capacity bound to prevent resource exhaustion
```

## Resolution

When N02 fires, at least one place in the Petri net can accumulate unboundedly
many tokens. The resolution depends on the grammar construct the place
represents:

1. **Add a capacity bound.** If the place represents a channel or buffer,
   introduce a grammar construct that limits the number of pending items.
   For example, a bounded channel `"chan" "[" <int> "]"` where the integer
   specifies the capacity.

2. **Introduce back-pressure.** Add synchronization between producers and
   consumers so that the producer blocks when the buffer is full. This
   converts the unbounded place into a bounded one at the cost of potential
   deadlock (see [N01](N01-deadlock-risk.md)).

3. **Ensure consumption rate.** If the grammar's semantics guarantee that
   tokens are consumed at least as fast as they are produced, the warning
   may be a false positive from the coverability analysis (which considers
   all interleavings, including pathological ones). Document the expected
   consumption rate.

4. **Accept the risk.** If the grammar models an inherently unbounded
   construct (e.g., an infinite input stream), the unbounded place is
   intentional. The warning serves as documentation of the resource model.

## Hint Explanation

The hint "consider adding a capacity bound to prevent resource exhaustion"
suggests the most direct mitigation: cap the number of tokens that can
accumulate in the place. A capacity bound converts the Karp-Miller omega
marker into a finite number, guaranteeing that the parser's memory usage
for that particular buffer is bounded. The trade-off is that a capacity
bound may introduce blocking behavior (the producer must wait when the
buffer is full), which could create new deadlock risks detectable by
[N01](N01-deadlock-risk.md).

## Related Lints

- [N01](N01-deadlock-risk.md) -- Deadlock risk; adding capacity bounds to unbounded places may introduce deadlocks
- [S01](../../safety/S01-safety-violation.md) -- Safety violation; unbounded growth may lead to bad parser configurations
- [P02](../../performance/P02-high-nfa-spillover.md) -- NFA spillover; unbounded token accumulation can cause excessive NFA buffer usage
