# N01: deadlock-risk

**Severity:** Warning
**Category:** analysis/concurrency
**Feature Gate:** `petri`

## Description

Detects potential deadlocks in the grammar's concurrency structure by modeling
parallel composition operators as Petri net transitions and analyzing the
resulting net for reachable dead markings. A *deadlock* occurs when the parser
reaches a state where no transition is enabled -- no rule can fire and no
progress can be made. In a grammar with parallel composition (e.g., `Proc "|"
Proc`), this corresponds to a situation where two or more concurrent parse
branches are each waiting for a token that the other branch must produce first.

The analysis works by translating the grammar into a Petri net:

- **Places** represent parser states (category entry points, rule midpoints,
  token buffers).
- **Transitions** represent rule applications (consuming tokens from input
  places, producing tokens in output places).
- **Tokens** represent available parser resources (unconsumed input tokens,
  partially constructed AST nodes).

A *dead marking* is a marking (token distribution) where no transition has all
its input places marked -- the system is stuck. The analysis uses *coverability*
to determine whether any dead marking is reachable from the initial marking.

### Petri net deadlock example

The following diagram shows a Petri net derived from a grammar with two parallel
processes that communicate via channels. The deadlock occurs when each process
is waiting for input on the channel that the other process should provide:

```
  ┌─────────────────────────────────────────────────────────┐
  │                    Petri Net Model                       │
  │                                                         │
  │   Initial marking: M_0 = {p_send1: 1, p_send2: 1}      │
  │                                                         │
  │          p_send1                    p_send2              │
  │         (  *  )                    (  *  )              │
  │            │                          │                  │
  │            v                          v                  │
  │      ┌───────────┐            ┌───────────┐             │
  │      │  t_send1  │            │  t_send2  │             │
  │      │ (send!ch1)│            │ (send!ch2)│             │
  │      └─────┬─────┘            └─────┬─────┘             │
  │            │                        │                    │
  │            v                        v                    │
  │         p_ch1                    p_ch2                   │
  │         (    )                   (    )                  │
  │            │                        │                    │
  │            v                        v                    │
  │      ┌───────────┐            ┌───────────┐             │
  │      │  t_recv2  │            │  t_recv1  │             │
  │      │ (recv?ch1)│            │ (recv?ch2)│             │
  │      └─────┬─────┘            └─────┬─────┘             │
  │            │                        │                    │
  │            v                        v                    │
  │         p_done2                  p_done1                 │
  │         (    )                   (    )                  │
  │                                                         │
  │   Deadlock marking: M_dead = {p_send1: 0, p_send2: 0,  │
  │     p_ch1: 0, p_ch2: 0, p_done1: 0, p_done2: 0}       │
  │                                                         │
  │   No transition enabled: t_recv1 needs p_ch2 (empty),   │
  │   t_recv2 needs p_ch1 (empty), t_send1/t_send2 already  │
  │   fired. System is stuck if send/recv ordering requires  │
  │   ch1 before ch2 but ch2 before ch1.                    │
  └─────────────────────────────────────────────────────────┘

  Legend:
    (  *  ) = place with 1 token (marked)
    (    )  = place with 0 tokens (unmarked)
    t_xxx   = transition (rule application)
    p_xxx   = place (parser state / channel buffer)
```

In the scenario above, if the grammar's operational semantics require that
`t_send1` fires before `t_recv1` can consume from `p_ch1`, and similarly
`t_send2` before `t_recv2`, then the only feasible execution order is
`t_send1 -> t_send2 -> t_recv2 -> t_recv1` (or `t_send2 -> t_send1 -> ...`).
But if the grammar's parallel composition operator does not impose this
ordering and instead allows interleaving where both `t_recv` transitions
are attempted before any `t_send`, deadlock occurs.

### Coverability analysis

The analysis uses the Karp-Miller coverability tree (see also
[N02](N02-unbounded-channel.md)) to determine whether a dead marking is
reachable. A marking M is *dead* if:

  forall t in T . exists p in pre(t) . M(p) < W(p, t)

where pre(t) is the set of input places of transition t, and W(p, t) is the
arc weight from place p to transition t.

## Trigger Conditions

A warning is emitted when **all** of the following conditions hold:

1. The `petri` feature is enabled.
2. The pipeline's Petri net module (`petri.rs`) has been executed, producing a
   `PetriAnalysis`.
3. The result's `has_deadlock_risk` field is `true`.

The lint is silent when:
- The `petri` feature is not enabled.
- No `PetriAnalysis` is available (analysis was not run).
- The `has_deadlock_risk` field is `false` (no dead markings reachable).

## Example

### Grammar

```
language! {
    name: ConcLang;
    primary: Proc;

    category Proc {
        Send  = "send" "!" Chan "(" Expr ")";
        Recv  = "recv" "?" Chan "(" Name ")";
        Par   = Proc "|" Proc;
        Seq   = Proc ";" Proc;
        Zero  = "0";
    }

    category Chan {
        ChanId = <ident>;
    }

    category Expr {
        native_type: Integer;
        IntLit = <int>;
    }

    category Name {
        Ident = <ident>;
    }
}
```

The parallel composition operator `Par` creates two concurrent parse branches.
If both branches contain `Recv` operations on channels that are only populated
by the other branch's `Send`, the Petri net analysis detects a potential
deadlock.

### Output

```
warning[N01] (ConcLang): Petri net coverability detects potential deadlock (4 places, 3 transitions)
  = hint: review parallel composition operators for potential blocking patterns
```

## Resolution

When N01 fires, the grammar's concurrency structure admits at least one
execution ordering that leads to deadlock. The resolution depends on the
grammar's intended semantics:

1. **Reorder operations.** If the grammar allows the author to specify
   execution order, ensure that send operations precede their corresponding
   receives within each parallel branch.

2. **Add synchronization.** Introduce explicit synchronization constructs
   (e.g., barriers, locks) that enforce a valid ordering of concurrent
   operations.

3. **Remove parallel composition.** If the deadlock is an artifact of the
   grammar allowing more concurrency than intended, replace `Proc "|" Proc`
   with sequential composition `Proc ";" Proc` in the affected rules.

4. **Add buffering.** If the channels are unbounded (see [N02](N02-unbounded-channel.md)),
   the deadlock may be avoidable by ensuring that senders can always proceed
   without waiting for receivers. Review the channel capacity model.

5. **Accept the risk.** If the deadlock is a property of the *language* being
   parsed (not the parser itself), the warning may be intentional. The grammar
   faithfully models a concurrent language where deadlocks are possible at the
   object-language level. In this case, the warning serves as documentation.

## Hint Explanation

The hint "review parallel composition operators for potential blocking patterns"
directs attention to the grammar rules that introduce concurrency. Parallel
composition operators (e.g., `Proc "|" Proc`) are the sole source of concurrent
parse branches. The deadlock necessarily involves at least two branches created
by such an operator, where each branch is blocked waiting for a resource (token,
channel value, or partially parsed node) that the other branch should produce.
Reviewing these operators and their child rules reveals the blocking cycle.

## Related Lints

- [N02](N02-unbounded-channel.md) -- Unbounded channel capacity; unbounded places can prevent deadlock (no blocking on full) but introduce other resource risks
- [N03](N03-scope-violation.md) -- Scope violations in name bindings; may co-occur with deadlock when binding scopes cross parallel branches
- [S01](../../safety/S01-safety-violation.md) -- Safety violation via WPDS prestar; deadlock-prone configurations may also appear as bad states in the WPDS model
