# A01: fixpoint-non-convergence

**Severity:** Warning
**Category:** Equation/rewrite termination analysis (historical `A` identifier)
**Feature Gate:** none (always active)

## Description

Detects grammar rules whose syntactic structure suggests **unbounded term
growth** under repeated rewriting. When a rule has two or
more self-referential nonterminals (nonterminals whose category matches the
rule's own category) and at most one terminal token, the rule can generate
progressively deeper terms on every rewrite cycle without a corresponding
structural reduction to bound the growth.

Consider a category `Proc` with a rule:

```
Wrap . p:Proc, q:Proc |- p : Proc;
```

The rule's RHS syntax contains two `Proc`-typed nonterminals and zero
terminals. If `Wrap` is used in a rewrite context, each cycle may replace a `Proc` sub-term with
`Wrap(p', q')`, producing a term one level deeper.  Without a complementary
depth-reducing rule (e.g., `Unwrap . p:Proc |- p : Proc;`), this growth is
unbounded and rewrite closure may not converge within practical time
or memory limits.

```
  Iteration 0:   t
  Iteration 1:   Wrap(t, t)
  Iteration 2:   Wrap(Wrap(t, t), Wrap(t, t))
  Iteration 3:   Wrap(Wrap(Wrap(...), ...), ...)
                  ↑
                  depth doubles each iteration
```

The lint uses a static heuristic: it counts the self-referential nonterminals
and terminal tokens in each rule's syntax.  If `self_refs >= 2` and
`terminals <= 1`, the rule is flagged.  This does not guarantee
non-convergence -- it identifies structural risk patterns.

## Trigger Conditions

All of the following must hold:

- The rule's syntax contains two or more nonterminals whose category matches
  the rule's own category (self-referential nonterminals).
- The rule's syntax contains at most one terminal token.
- The rule has at least two nonterminals total.

One diagnostic is emitted per flagged rule.

## Example

### Grammar

```rust
language! {
    name: TreeLang,
    types {
        ![String] as Proc
    },
    terms {
        Leaf  . |- "leaf" : Proc;
        // Two self-referential NTs, zero terminals:
        Wrap  . p:Proc, q:Proc |- p : Proc;
    },
}
```

### Output

```
warning[A01] (TreeLang): rule `Wrap` has 2 self-referential nonterminals with 0 terminal(s) — potential unbounded term growth under repeated rewriting
  = hint: orient the rules around a well-founded decreasing measure, remove redundant growth rules, or isolate the recursive family into an independently measured rewrite stratum
```

## Resolution

1. **Add a depth-reducing rule.**  Introduce a rewrite that collapses nested
   applications of the flagged constructor.  For instance, adding
   `|- Wrap(Wrap(x, y), z) ~> Wrap(x, z) ;` ensures that double-nesting is
   reduced, giving the rewrite family a decreasing structural measure.

2. **Prove a well-founded orientation.** Choose a size, precedence, or
   dependency rank that strictly decreases on every cycle. This preserves
   completeness instead of discarding terms at an arbitrary depth.

3. **Factor independent recursive families.** Isolate rules that do not need
   simultaneous closure, then measure the work and resident-set size of each
   stratum independently.

4. **Accept the warning.**  If the grammar intentionally builds deep recursive
   structures (e.g., for tree languages), rewrite closure may still converge
   if other rules act as reducers. Verify convergence empirically and suppress
   this warning via `PRATTAIL_LINT_LEVEL=error`.

## Hint Explanation

The hint names three semantics-preserving strategies:

- **Depth-reducing rules** are rewrites whose LHS pattern has greater depth
  than their RHS.  If every depth-increasing rule has a corresponding
  depth-reducing counterpart, closure may reach a stable state where
  growth and reduction balance out.

- A **well-founded measure** proves that no cycle can grow forever.
- An **independent stratum** removes irrelevant cross-family propagation and
  gives the remaining resource cost a measurable service-level policy. None
  of these repairs imposes an artificial traversal-depth ceiling.

## Related Lints

- [A04](A04-large-equivalence-class.md) -- Equivalence class explosion can
  amplify the effects of unbounded term growth, since each new deep term must
  be classified into equivalence classes.
- [A07](A07-fixpoint-iteration-anomaly.md) -- Reports when the grammar's
  overall dependency structure suggests a high iteration count, which
  compounds with A01-style growth.
- [T03](../analysis/trs/T03-non-terminating-cycle.md) -- Termination analysis
  detects actual non-terminating rewrite cycles, complementing A01's static
  structural heuristic.
