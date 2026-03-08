# T03: non-terminating-cycle

**Severity:** Warning
**Category:** analysis/trs
**Feature Gate:** `trs-analysis`

## Description

Detects potential non-termination in the grammar's term rewriting system (TRS).
The analysis constructs a **dependency graph** from the rewrite rules and
computes its strongly connected components (SCCs). Each SCC represents a set of
rules that can mutually trigger each other, forming a potential rewriting cycle.
If no decreasing measure (a well-founded ordering that strictly decreases with
each step) can be established for an SCC, the system may loop indefinitely.

A TRS R is **terminating** (strongly normalizing, SN) when there is no infinite
reduction sequence:

    t₀ ->_R t₁ ->_R t₂ ->_R ...

Termination is undecidable in general, but sufficient conditions exist. The
standard approach is to find a **reduction ordering** succ (a well-founded
strict partial order closed under contexts and substitutions) such that for
every rule l -> r in R, l succ r. The dependency pair method refines this by
decomposing the problem into SCCs of the dependency graph and requiring a
decreasing ordering only within each SCC.

When the analysis cannot find a decreasing measure for one or more SCCs, T03
fires with the count of problematic SCCs and a human-readable reason.

```
  Dependency Graph with SCCs
  ══════════════════════════

  ┌─────────────┐     ┌─────────────┐
  │   SCC 0     │     │   SCC 1     │
  │ ┌─────────┐ │     │ ┌─────────┐ │
  │ │ Rule 2  │◄├─────┤►│ Rule 4  │ │
  │ │ f(g(x)) │ │     │ │ h(f(x)) │ │
  │ │  -> ... │ │     │ │  -> ... │ │
  │ └────┬────┘ │     │ └────┬────┘ │
  │      │      │     │      │      │
  │      v      │     │      v      │
  │ ┌─────────┐ │     │ ┌─────────┐ │
  │ │ Rule 3  │ │     │ │ Rule 5  │ │
  │ │ g(f(x)) │ │     │ │ f(h(x)) │ │
  │ │  -> ... ├─┼─┐   │ │  -> ... │ │
  │ └─────────┘ │ │   │ └─────────┘ │
  └─────────────┘ │   └─────────────┘
           ▲      │
           └──────┘
    SCC 0: cycle      SCC 1: no measure
    Rules 2 <-> 3     Rules 4 <-> 5
                       T03 fires for SCC 1
```

In the diagram above, SCC 0 has a decreasing measure (e.g., the size of the
term decreases), but SCC 1 does not -- the rules in SCC 1 can cycle
indefinitely because f and h interact without any size or weight decrease.

## Trigger Conditions

All of the following must hold:

- The `trs-analysis` feature is enabled at compile time.
- A `TerminationResult` is available in the lint context.
- The result is `PotentiallyNonTerminating`, meaning at least one SCC in the
  dependency graph could not be shown to have a decreasing measure within the
  analysis bounds.

Exactly one T03 diagnostic is emitted per grammar, reporting the total count of
problematic SCCs and the reason string.

## Example

### Grammar

```rust
language! {
    name: InfiniteSwap,
    types {
        ![String] as Term
    },
    terms {
        Var . |- <ident> : Term;
        F   . x:Term |- "f" "(" x ")" : Term;
        G   . x:Term |- "g" "(" x ")" : Term;

        // Rewrite rules that form a non-terminating cycle:
        // Rule 0:  f(g(x)) -> g(f(x))   (swap f and g)
        // Rule 1:  g(f(x)) -> f(g(x))   (swap g and f)
        //
        // These two rules form an SCC: applying Rule 0 produces a term
        // that matches Rule 1, and vice versa, indefinitely:
        //   f(g(a)) -> g(f(a)) -> f(g(a)) -> ...
    },
}
```

### Output

```
warning[T03] (InfiniteSwap): potential non-termination: cycle in SCC (1 problematic SCC(s))
  = hint: add a decreasing measure or simplify the rewrite cycle
```

## Resolution

1. **Introduce a decreasing measure.** Add a weight, size, or lexicographic
   ordering that strictly decreases with each rule application in the
   problematic SCC. For example, if the swap rules are meant to sort symbols,
   assign an ordering f > g and require that the outer function symbol must
   be greater than the inner one after rewriting.

2. **Break the cycle.** Remove or modify one of the rules in the SCC so that
   the mutual triggering relationship no longer forms a cycle. In the example,
   deleting Rule 1 eliminates the loop, leaving only a one-directional
   normalization (f-over-g becomes g-over-f, then stops).

3. **Add a termination guard.** Introduce an auxiliary constructor or flag that
   tracks reduction depth. For instance, wrapping terms in a `Step(n, t)`
   constructor where n decreases ensures termination by bounded descent:
   `f(g(Step(n, x))) -> g(f(Step(n-1, x)))` with a base case at n = 0.

4. **Accept non-termination.** If the grammar models a system that inherently
   permits infinite reductions (e.g., an untyped lambda calculus), this warning
   can be acknowledged as expected behavior. The grammar author should document
   that a specific reduction strategy (e.g., lazy evaluation, bounded search) is
   used at runtime to avoid divergence.

## Hint Explanation

The hint **"add a decreasing measure or simplify the rewrite cycle"** identifies
the two fundamental approaches to establishing termination:

- A **decreasing measure** is a function mu from terms to a well-founded set
  (W, >) such that for every rule l -> r in the problematic SCC,
  mu(l sigma) > mu(r sigma) for all substitutions sigma. Common choices include:
    - **Term size:** |t| = 1 + sum of subtree sizes. Works when rules reduce
      the number of constructors.
    - **Knuth-Bendix ordering:** A weighted extension of the subterm ordering
      parameterized by function-symbol weights and a precedence.
    - **Lexicographic path ordering (LPO):** Compares terms lexicographically
      on their outermost function symbols, then recursively on arguments.
    - **Polynomial interpretation:** Maps each function symbol to a polynomial
      and checks that l's polynomial is strictly greater than r's.

- **Simplifying the rewrite cycle** means altering the rules so the SCC either
  disappears (the dependency pairs no longer form a cycle) or shrinks to a
  trivially terminating component. This is often the simpler fix when the
  cycling rules represent an unintended interaction.

## Related Lints

- [T04](T04-termination-verified.md) -- The positive counterpart: emitted when
  all SCCs have decreasing measures, confirming termination.
- [T01](T01-non-joinable-critical-pair.md) -- A non-terminating system cannot
  be completed by Knuth-Bendix completion (which requires termination to orient
  new equations). If both T01 and T03 fire, the TRS has both confluence and
  termination problems.
- [T02](T02-confluence-verified.md) -- If T02 fires but T03 also fires, the
  system is confluent but potentially non-terminating -- a valid but unusual
  configuration.
