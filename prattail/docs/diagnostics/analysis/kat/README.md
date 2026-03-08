# KAT Analysis Diagnostics (K-Category)

**Date:** 2026-03-08
**Source:** `prattail/src/lint.rs` (emission), `prattail/src/kat.rs` (Kleene Algebra with Tests)

## 1 Overview

The K-category lints report results from Kleene Algebra with Tests (KAT) analysis of the grammar's parse control flow. KAT extends Kleene algebra with a Boolean subalgebra of tests (predicates), yielding a decidable equational theory that subsumes propositional Hoare logic. This enables automated verification of parse program specifications and behavioral equivalence of grammar transformations.

```
  Parse Program Specifications
               |
       ┌───────┴───────┐
       |               |
       v               v
  ┌───────────┐   ┌────────────┐
  │  Hoare    │   │ Equivalence │
  │  Triples  │   │   Checks    │
  │ {p} e {q} │   │  e_1 =? e_2 │
  └───────────┘   └────────────┘
       |               |
       v               v
  test(p).e.       Automata-
  test(not q)      based
  =? 0             bisimulation
       |               |
       v               v
  ┌────┴────┐     ┌────┴────┐
  |         |     |         |
  v         v     v         v
Valid    Invalid  Equiv   Inequiv
(silent)   |       |         |
           v       └────┬────┘
          K01            v
        (Warning)       K02
                      (Note)
```

Both K-category lints require the `kat` feature gate to be enabled at compile time.

## 2 Lint Index

| ID | Severity | Name | Description |
|----|----------|------|-------------|
| [K01](K01-hoare-failure.md) | Warning | hoare-failure | Hoare triple `{p} e {q}` fails: `test(p) . e . test(not q) != 0` |
| [K02](K02-kat-equivalence.md) | Note | kat-equivalence | KAT equivalence result: `e_1 equiv e_2` or `e_1 not equiv e_2` |

## 3 Theoretical Background

### 3.1 KAT Axioms

A Kleene Algebra with Tests `(K, B, +, ., *, 0, 1)` satisfies:

**Kleene algebra axioms:**

```
(K, +, 0) is an idempotent commutative monoid:
    p + q = q + p                          (commutativity of +)
    p + (q + r) = (p + q) + r              (associativity of +)
    p + 0 = p                              (identity for +)
    p + p = p                              (idempotence of +)

(K, ., 1) is a monoid:
    p . (q . r) = (p . q) . r              (associativity of .)
    p . 1 = 1 . p = p                      (identity for .)

Distributivity and annihilation:
    p . (q + r) = p . q + p . r            (left distributivity)
    (p + q) . r = p . r + q . r            (right distributivity)
    p . 0 = 0 . p = 0                      (annihilation)

Natural ordering:
    p <= q  iff  p + q = q                 (semilattice order)

Star axioms:
    1 + p . p* <= p*                       (unfolding)
    q + p . r <= r  implies  p* . q <= r   (left induction)
    q + r . p <= r  implies  q . p* <= r   (right induction)
```

**Boolean test axioms (for b, c in B):**

```
b + not b = 1                              (excluded middle)
b . not b = 0                              (non-contradiction)
b . c = c . b                              (commutativity of tests)
```

### 3.2 Hoare Logic Embedding

The correspondence between Hoare logic rules and KAT equations:

| Hoare Rule | KAT Encoding |
|------------|-------------|
| `{p} skip {p}` | `test(p) . 1 . test(not p) = 0` |
| `{p} e1;e2 {r}` given `{p} e1 {q}` and `{q} e2 {r}` | Follows from `test(p).e1.test(not q) = 0` and `test(q).e2.test(not r) = 0` |
| `{p /\ b} e1 {q}`, `{p /\ not b} e2 {q}` implies `{p} if b then e1 else e2 {q}` | `test(p).(test(b).e1 + test(not b).e2).test(not q) = 0` |
| `{p /\ b} e {p}` implies `{p} while b do e {p /\ not b}` | `test(p).(test(b).e)*.test(not(p /\ not b)) = 0` |

### 3.3 Complexity

| Operation | Complexity |
|-----------|------------|
| KAT equivalence (general) | PSPACE-complete |
| Hoare triple validity | PSPACE-complete (reduces to KAT equivalence) |
| Bounded bisimulation (implementation) | O(2^k x n^2) where k = atomic tests, n = expression size |

## 4 PraTTaIL Integration

KAT models PraTTaIL's parse control flow at the level of individual parse functions. The mapping between parse concepts and KAT constructs is:

| Parse Concept | KAT Construct |
|---------------|---------------|
| Sequential parsing | `.` (composition) |
| Alternative dispatch | `+` (alternation) |
| Recursive category | `*` (Kleene star) |
| Token predicate | Boolean test (`b in B`) |
| Parse action (shift/reduce) | Atomic action (`p in K`) |
| Parse failure | `0` (zero) |
| Skip / epsilon | `1` (one) |

Typical Hoare triples for parser verification:

- `{token_available} parse_expr {ast_node_created}` -- parsing an expression produces an AST node.
- `{in_recovery} sync_to_semicolon {not in_recovery}` -- recovery terminates after synchronization.
- `{balanced_parens} parse_paren_expr {balanced_parens}` -- parenthesized expression parsing preserves delimiter balance.

## 5 Related Diagnostic Categories

- **L (Temporal):** LTL model checking verifies infinite-trace properties; KAT verifies finite-trace pre/post specifications. They are complementary: KAT handles sequential/compositional reasoning, LTL handles liveness and fairness.
- **M (Morphism):** KAT equivalence can verify that morphism-translated programs preserve behavior.
- **E (Extension):** CRA cost analysis quantifies parse execution cost; KAT verifies qualitative correctness.
- **P (Performance):** P06 reports total analysis phase time, which includes KAT analysis.
