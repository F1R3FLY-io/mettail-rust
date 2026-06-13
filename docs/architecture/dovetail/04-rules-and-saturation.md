# Rules and Saturation

Dovetail represents rewrite rules as data. A caller supplies `RewriteRule<L>`
values over payload labels `L`.

## Rule Shape

A rule has:

| Field | Meaning |
|---|---|
| `lhs` | pattern matched against e-classes |
| `rhs` | pattern instantiated under a match substitution |
| `label` | optional diagnostic name |

Patterns are:

`Pattern = Var(name) | App(op, args)`

A substitution maps variable names to e-classes:

`Subst : variableName ↦ EClassId`

## Search And Instantiation

Rule matching is structural over e-nodes. A variable binds to an e-class. If the
same variable appears twice, both occurrences must resolve to the same canonical
e-class.

Literate pseudocode:

```text
To match a pattern against an e-class:
  If the pattern is a variable:
    If the variable is unbound, bind it to the canonical class.
    If it is already bound to this class, keep the match.
    Otherwise reject the match.
  If the pattern is an application:
    For each e-node in the class:
      Require the same operator and arity.
      Recursively match each child pattern against the child e-class.
```

Instantiation rejects ill-formed right-hand sides:

`vars(rhs) ⊆ vars(lhs)`

If a right-hand-side variable is unbound, Dovetail adds no partial term.

## Saturation Outcomes

Saturation has three terminal outcomes:

| Outcome | Meaning |
|---|---|
| `Converged` | an iteration produced no new merges |
| `NodeLimit` | the e-node budget refused a fresh node |
| `IterationLimit` | `max_iters` ended before convergence |

This is deliberately not a Boolean success flag. A caller must inspect the
outcome before treating extracted results as complete for a language.

## Saturation Algorithm

Literate pseudocode:

```text
To saturate an e-graph:
  For each iteration up to max_iters:
    Set the iteration merge count to zero.
    For each rewrite rule:
      Search all matches of the left-hand side.
      For each match:
        Reject the match if the right-hand side has an unbound variable.
        Instantiate the right-hand side inside the node budget.
        If the budget refuses a fresh node, return NodeLimit.
        Merge the match root with the instantiated right-hand side.
      If this rule caused merges, rebuild congruence closure.
    If the iteration caused no merges, return Converged.
  Return IterationLimit.
```

## Monotonicity

Saturation adds equality evidence; it does not replace a term with another term.

`Fᵢ ⊆ Fᵢ₊₁`

where `Fᵢ` is the set of represented equality facts after iteration `i`.

This monotonicity is why extraction can enumerate alternatives after
saturation rather than relying on saturation to choose a winner.

## Budget Discipline

`try_add_with_budget` refuses a fresh node before overshooting:

`node_count ≤ max_nodes`

An existing exact node can still be resolved after the budget is reached,
because resolving a duplicate does not grow the graph.
