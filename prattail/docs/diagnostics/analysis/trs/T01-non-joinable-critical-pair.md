# T01: non-joinable-critical-pair

**Severity:** Warning
**Category:** analysis/trs
**Feature Gate:** `trs-analysis`

## Description

Detects critical pairs in the grammar's term rewriting system (TRS) that fail to
join -- two rewrite sequences that diverge from a common ancestor but never
reconverge to a shared normal form. This is the fundamental witness of a
**confluence failure**: the system produces different results depending on which
rule fires first.

A term rewriting system R = {l_i -> r_i} is **confluent** (Church-Rosser) when
for every term t, if t ->* u and t ->* v, then there exists a term w such that
u ->* w and v ->* w. The Knuth-Bendix critical pair theorem (1970) reduces this
global property to a finite check: R is confluent if and only if every critical
pair is joinable.

A **critical pair** arises when two rules overlap. Given rules:

    l₁ -> r₁  and  l₂ -> r₂

if there is a non-variable position p in l₂ such that the subterm l₂|_p unifies
with l₁ via most general unifier sigma, then the critical pair is:

    CP = langle r₁sigma,  l₂[r₂]_p sigma rangle

The pair is **joinable** (written r₁sigma downarrow l₂[r₂]_p sigma) when both
sides reduce to a common term under ->*. When they do not, T01 fires.

```
         t = l₂sigma
        / \
       /   \
      /     \
  rule₁     rule₂
  at p      full
    /         \
   v           v
  r₁sigma    l₂[r₂]_p sigma
   |           |
   v           v
  u₁          u₂       u₁ ≠ u₂  =>  T01 fires
   \     ???  /
    \   ???  /
     v     v
       ???           no common reduct exists
```

When the fork diagram above cannot be completed -- when no term w satisfies
u₁ ->* w and u₂ ->* w -- the system is not confluent and T01 reports the
offending pair.

## Trigger Conditions

All of the following must hold:

- The `trs-analysis` feature is enabled at compile time.
- A `ConfluenceAnalysis` result is available in the lint context (the pipeline
  ran confluence checking).
- At least one `CriticalPair` in the analysis has a corresponding
  `JoinabilityResult::NotJoinable` entry (the pair's two reducts do not share a
  common normal form within the analysis reduction bound).

One diagnostic is emitted per non-joinable critical pair.

## Example

### Grammar

```rust
language! {
    name: ArithSimplify,
    types {
        ![i32] as Expr
    },
    terms {
        Num   . n:Expr |- n : Expr;
        Add   . a:Expr, b:Expr |- a "+" b : Expr;
        Mul   . a:Expr, b:Expr |- a "*" b : Expr;
        Neg   . a:Expr |- "-" a : Expr;

        // Rewrite rules with overlapping LHS patterns:
        // Rule 0:  -(x + y)  ->  (-x) + (-y)    (distribute negation)
        // Rule 1:  -(-(z))   ->  z               (double negation)
        //
        // Overlap at Neg(Neg(Add(a,b))): Rule 0 applies to Neg(Add(a,b)),
        // Rule 1 applies to Neg(Neg(...)).
        //
        // Rule 0 yields: Neg(Add(a,b)) -> Add(Neg(a), Neg(b))
        //   then outer Neg: Neg(Add(Neg(a), Neg(b)))
        //     -> Add(Neg(Neg(a)), Neg(Neg(b)))
        //
        // Rule 1 yields: Neg(Neg(Add(a,b))) -> Add(a,b)
        //
        // These diverge: Add(Neg(Neg(a)), Neg(Neg(b))) vs Add(a,b)
        // Rule 1 could reduce the first further, but only with extra steps
        // not guaranteed by the analysis bound.
    },
}
```

### Output

```
warning[T01] (ArithSimplify): critical pair (rules 0, 1) is not joinable — confluence failure: Add(Neg(Neg(a)), Neg(Neg(b))) ≠ Add(a, b)
  = hint: add an equation or oriented rewrite to make the terms joinable
```

## Resolution

1. **Add an oriented rewrite rule.** The Knuth-Bendix completion procedure
   suggests adding an oriented equation that makes the two reducts joinable. In
   the example, adding a rule `Neg(Neg(x)) -> x` (double-negation elimination)
   at sufficiently high priority would allow `Add(Neg(Neg(a)), Neg(Neg(b)))` to
   reduce to `Add(a, b)`, closing the fork.

2. **Add an unoriented equation.** If no natural orientation exists, introduce
   an equation (treated as a bidirectional rewrite) that equates the two normal
   forms. This relaxes the rewriting system from a TRS to an equational system,
   but ensures that equivalent terms are recognized as equal.

3. **Restrict rule overlap.** Refine the LHS patterns so the two rules no
   longer overlap at a non-variable position. For instance, adding a guard or
   side condition to Rule 0 that excludes the case where the inner term is
   itself a negation would eliminate the critical pair entirely.

4. **Accept the non-confluence.** If the grammar intentionally supports
   non-deterministic rewriting (e.g., for search or enumeration), suppress this
   warning by acknowledging that the system's evaluation order matters.

## Hint Explanation

The hint **"add an equation or oriented rewrite to make the terms joinable"**
refers to the two standard strategies from Knuth-Bendix completion theory:

- An **oriented rewrite** l -> r adds a new rule to the TRS, chosen so that the
  two previously non-joinable reducts can now be reduced to a common term. The
  orientation must be compatible with a well-founded ordering (e.g., the
  Knuth-Bendix ordering or a lexicographic path ordering) to preserve
  termination.

- An **equation** l = r is the unoriented version: it declares the two sides
  equivalent without choosing a reduction direction. This is always safe for
  confluence but may complicate termination analysis and normal-form computation.

The key insight is that every non-joinable critical pair is a **witness** -- it
identifies exactly which two rule interactions need reconciliation. The hint
directs the author to the minimal fix: one new equation per non-joinable pair.

## Related Lints

- [T02](T02-confluence-verified.md) -- The positive counterpart: emitted when
  all critical pairs are joinable, confirming confluence.
- [T03](T03-non-terminating-cycle.md) -- Termination analysis may interact with
  confluence: a non-terminating TRS cannot be completed by Knuth-Bendix
  (completion requires termination for orientation).
- [T04](T04-termination-verified.md) -- If both T02 and T04 fire, the TRS is
  convergent (confluent + terminating), the ideal state for a rewriting system.
