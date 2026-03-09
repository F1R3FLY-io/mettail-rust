# A01: fixpoint-non-convergence

**Severity:** Warning
**Category:** Ascent / Fixpoint Analysis
**Feature Gate:** none (always active)

## Description

Detects grammar rules whose syntactic structure suggests **unbounded term
growth** during Ascent Datalog fixpoint computation.  When a rule has two or
more self-referential nonterminals (nonterminals whose category matches the
rule's own category) and at most one terminal token, the rule can generate
progressively deeper terms on every fixpoint iteration without a corresponding
structural reduction to bound the growth.

Consider a category `Proc` with a rule:

```
Wrap . p:Proc, q:Proc |- p : Proc;
```

The rule's RHS syntax contains two `Proc`-typed nonterminals and zero
terminals.  During Ascent's fixpoint evaluation, if `Wrap` is used in a
rewrite context, each iteration may replace a `Proc` sub-term with
`Wrap(p', q')`, producing a term one level deeper.  Without a complementary
depth-reducing rule (e.g., `Unwrap . p:Proc |- p : Proc;`), this growth is
unbounded and the fixpoint iteration may not converge within practical time
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
warning[A01] (TreeLang): rule `Wrap` has 2 self-referential nonterminals with 0 terminal(s) — potential unbounded term growth in fixpoint computation
  = hint: ensure complementary depth-reducing rules exist, or add a depth bound
```

## Resolution

1. **Add a depth-reducing rule.**  Introduce a rewrite that collapses nested
   applications of the flagged constructor.  For instance, adding
   `|- Wrap(Wrap(x, y), z) ~> Wrap(x, z) ;` ensures that double-nesting is
   reduced, bounding the maximum depth growth per iteration.

2. **Add a depth bound.**  Use the `ART05_DepthBound` optimization to set a
   compile-time limit on term depth during fixpoint evaluation.  Terms
   exceeding the bound are discarded or approximated, guaranteeing
   termination at the cost of completeness.

3. **Increase terminal coverage.**  Adding terminals to the rule's syntax
   (e.g., a delimiting keyword or punctuation) increases the structural
   entropy per iteration, naturally limiting how quickly terms can grow.

4. **Accept the warning.**  If the grammar intentionally builds deep recursive
   structures (e.g., for tree languages), the fixpoint may still converge if
   other rules act as reducers.  Verify convergence empirically and suppress
   this warning via `PRATTAIL_LINT_LEVEL=error`.

## Hint Explanation

The hint **"ensure complementary depth-reducing rules exist, or add a depth
bound"** directs the author to two strategies:

- **Depth-reducing rules** are rewrites whose LHS pattern has greater depth
  than their RHS.  If every depth-increasing rule has a corresponding
  depth-reducing counterpart, the fixpoint may reach a stable state where
  growth and reduction balance out.

- A **depth bound** is a hard ceiling on the term depth maintained during
  fixpoint evaluation.  The `ART05_DepthBound` codegen optimization prunes
  terms that exceed the bound, converting potential non-termination into a
  bounded (but possibly approximate) analysis.

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
