# S01: safety-violation

**Severity:** Warning
**Category:** analysis/safety
**Feature Gate:** always-on

## Description

A grammar defines a set of reachable parser configurations -- states the parser
can enter when dispatching rules, descending into categories, and returning from
cross-category calls. Some of these configurations may be *bad*: they correspond
to parser states that should never be entered (unreachable-yet-dispatched rules,
ill-formed cross-category transitions, or nonsensical stack configurations).
S01 fires when the WPDS prestar analysis proves that at least one bad state is
reachable from the grammar's initial configuration.

The intuition is straightforward. A weighted pushdown system (WPDS) models the
parser's inter-procedural control flow: categories are procedures, rules are
intraprocedural transitions, and cross-category calls push/pop stack symbols.
The *prestar* algorithm saturates a P-automaton backwards from a set of target
(bad) configurations, adding transitions until a fixed point is reached. If the
initial configuration's weight is non-zero after saturation, a witness path from
an initial state to a bad state exists.

Formally, let P = (P, Gamma, Delta, S) be the WPDS and let A_bad be the
P-automaton accepting bad configurations. Prestar computes:

  pre*(A_bad) = { c in Conf(P) | exists c' in L(A_bad) . c =>* c' }

S01 fires when the initial configuration c_0 in L(pre*(A_bad)), i.e. the
initial weight w(c_0) in pre*(A_bad) satisfies w(c_0) != 0.

### P-automaton saturation diagram

The following diagram shows how prestar adds transitions backwards from bad
states. Starting from the bad-state automaton A_bad, the saturation procedure
discovers that the initial configuration can reach the bad state through a chain
of push/pop transitions:

```
  A_bad (before saturation)            pre*(A_bad) (after saturation)
  ═══════════════════════════          ══════════════════════════════════

  ┌─────┐                             ┌─────┐
  │ p_0 │                             │ p_0 │─────────────┐
  └──┬──┘                             └──┬──┘             │
     │                                   │                │ (added by
     │ gamma_1                           │ gamma_1        │  saturation)
     v                                   v                v
  ┌─────┐                             ┌─────┐         ┌──────┐
  │ q_1 │                             │ q_1 │────────>│ q_bad │
  └─────┘                             └──┬──┘         └──────┘
                                         │                ^
                                         │ gamma_2        │ epsilon
                                         v                │
                                      ┌─────┐          ┌──────┐
                                      │ q_2 │─────────>│ q_acc │
                                      └─────┘          └──────┘

  Legend:
    p_0       = initial control state
    gamma_1   = stack symbol (category entry)
    q_1, q_2  = intermediate automaton states
    q_bad     = bad configuration accepting state
    q_acc     = acceptance state (epsilon-reachable)
    ─────>    = transition added by prestar saturation
```

The saturation procedure processes WPDS rules in reverse:

1. For a push rule (p, gamma) ->_w (p', gamma_1 gamma_2), prestar adds
   a transition from p to an intermediate state reading gamma, then from
   the intermediate state via gamma_1 and gamma_2 to reach q_bad.

2. For a pop rule (p, gamma) ->_w (p', epsilon), prestar collapses the
   stack by adding an epsilon-transition.

3. The fixed point is reached when no new transitions can be added.

When w(p_0, gamma_init) in pre*(A_bad) is non-zero, S01 fires with the
initial weight displayed in the diagnostic message.

## Trigger Conditions

A warning is emitted when **all** of the following conditions hold:

1. The pipeline's safety verification module (`verify.rs`) has been executed,
   producing a `SafetyResult`.
2. The result's `safe` field is `false`.
3. The `initial_weight` is non-zero (for `BooleanWeight`, this means `true`;
   for `TropicalWeight`, this means a finite cost).

The lint is silent when:
- No `SafetyResult` is available (analysis was not run).
- The result's `safe` field is `true` (no bad states reachable).

## Example

### Grammar

```
language! {
    name: ConcurrentCalc;
    primary: Proc;

    category Proc {
        Send  = "send" "!" "(" Expr ")";
        Recv  = "recv" "?" "(" Name ")";
        Par   = Proc "|" Proc;
    }

    category Expr {
        IntLit  = <int>;
        Add     = Expr "+" Expr;
    }

    category Name {
        Ident = <ident>;
    }

    // Phantom category: declared with rules but never reachable
    // from Proc -- the parser can dispatch into it via a stale
    // prediction WFST entry, creating a bad configuration.
    category Ghost {
        native_type: String;
        GhostLit = <string>;
        GhostOp  = Ghost "~" Ghost;
    }
}
```

### Output

```
warning[S01] (ConcurrentCalc): bad state reachable via WPDS prestar (initial weight: true)
  = hint: review the grammar for unreachable-yet-dispatched rules
```

## Resolution

When S01 fires, at least one bad configuration is reachable. The resolution
depends on the nature of the bad state:

1. **Orphan category:** A category exists in the grammar but has no cast or
   cross-category path from the primary category. The parser may still generate
   dispatch code for it, creating a reachable-but-meaningless configuration.
   **Fix:** Remove the category or add a cast/cross-category rule connecting it
   to the primary.

2. **Stale prediction entry:** The prediction WFST maps a token to a rule in a
   category that the WPDS call graph cannot reach. This indicates a mismatch
   between WFST dispatch and the actual inter-procedural call structure.
   **Fix:** Regenerate the WFST or remove the conflicting rule.

3. **Inconsistent stack depth:** A cross-category call chain creates a stack
   configuration that violates the expected depth invariant (e.g., unbounded
   recursion through a cycle of cast rules).
   **Fix:** Break the cast cycle (see [C01](../../cross-category/C01-cast-cycle.md)).

4. **Witness trace inspection:** The `SafetyResult` includes a `witness_trace`
   field containing the stack symbols along the path to the bad state. Inspect
   this trace to identify which cross-category call sequence leads to the
   violation.

## Hint Explanation

The hint "review the grammar for unreachable-yet-dispatched rules" points to the
most common root cause: a rule or category that the prediction WFST includes in
its dispatch table but that the WPDS inter-procedural analysis proves cannot
actually be reached through legitimate parser control flow. The presence of such
rules indicates a gap between the flat WFST model (which ignores the call stack)
and the pushdown model (which tracks it precisely). Reviewing the grammar for
orphan categories, stale cast rules, or unreachable cross-category paths will
typically reveal the source of the safety violation.

## Related Lints

- [S02](S02-safety-verified.md) -- The complementary note: emitted when prestar proves no bad states are reachable
- [S03](S03-cegar-refinement.md) -- CEGAR refinement loop that may discover safety violations through iterative abstraction refinement
- [W01](../../wfst/W01-dead-rule.md) -- Tier 1-4 dead-rule detection; S01 covers the pushdown-aware case
- [W13](../../wfst/W13-wpds-unreachable.md) -- WPDS stack-aware unreachability (Tier 5); closely related but targets rule-level unreachability rather than global safety
