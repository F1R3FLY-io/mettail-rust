# K02: kat-equivalence

**Severity:** Note
**Category:** analysis/kat
**Feature Gate:** `kat`

## Description

Reports the result of a KAT equivalence check between two Kleene Algebra with Tests expressions. KAT equivalence determines whether two parse programs (represented as KAT expressions) denote the same set of guarded strings -- that is, whether they are behaviorally indistinguishable under all possible Boolean test valuations.

K02 is an informational diagnostic: it reports both positive (`equiv`) and negative (`not equiv`) results. It does not distinguish between "good" and "bad" outcomes, since equivalence or inequivalence may be desirable depending on context (e.g., verifying that an optimization preserves behavior vs. confirming that two programs are genuinely different).

### Automata-Based Decision Procedure

KAT equivalence is decidable in PSPACE (Kozen & Smith, 1996). The implementation uses a bounded bisimulation procedure inspired by Pous (2015), which constructs automata for both expressions and checks language equivalence:

```
  KAT expressions:  e_1,  e_2
           |             |
           v             v
  ┌──────────────────────────────┐
  │  Compile to guarded-string   │
  │  automata                    │
  │                              │
  │  A_1 = automaton(e_1)        │
  │  A_2 = automaton(e_2)        │
  └──────────────────────────────┘
           |             |
           v             v
  ┌──────────────────────────────┐
  │  Bisimulation up to         │
  │  congruence (Pous, 2015)    │
  │                              │
  │  BFS exploration of the     │
  │  product A_1 x A_2          │
  │                              │
  │  At each state pair (q1,q2): │
  │  1. Check atom agreement     │
  │  2. Explore successors       │
  │  3. Apply congruence closure │
  └──────────────────────────────┘
           |
      ┌────┴────┐
      |         |
      v         v
  Bisimilar   Not bisimilar
      |         |
      v         v
   e_1 equiv e_2   e_1 not equiv e_2
   (K02: equiv)     (K02: not equiv)
```

### Guarded Strings

A guarded string over atoms `At` and actions `Act` is a sequence:

```
alpha_0 . p_1 . alpha_1 . p_2 . alpha_2 . ... . p_n . alpha_n
```

where each `alpha_i` is an atom (a complete Boolean valuation assigning true/false to each atomic test) and each `p_i` is an action. Guarded strings are the semantic domain of KAT: two expressions are equivalent iff they denote the same set of guarded strings.

The atoms partition the state space into equivalence classes. For `k` atomic tests, there are `2^k` atoms. Each atom represents a complete description of which predicates hold. Actions transition between atoms.

### What K02 Reports

K02 emits one diagnostic per equivalence check, showing both expressions and whether they are equivalent (`equiv`) or inequivalent (`not equiv`):

- `e_1 equiv e_2` -- the expressions denote the same set of guarded strings.
- `e_1 not equiv e_2` -- the expressions denote different sets; there exists a guarded string in one but not the other.

## Trigger Conditions

K02 fires once per equivalence check result. Specifically:

- The `kat` feature gate is enabled.
- The pipeline has computed a `KatCheck` result.
- The `equivalence_results` field contains at least one `(expr1, expr2, equivalent)` triple.
- One K02 diagnostic is emitted per equivalence check.

If no equivalence checks are configured, K02 is silent.

## Example

### Grammar

```
language! {
    name: OptLang;
    primary: Expr;

    category Expr {
        native_type: Integer;
        Num    = <int>;
        Add    = Expr "+" Expr;
        Mul    = Expr "*" Expr;
        Neg    = "-" Expr;
        Zero   = "0";
    }
}
```

With equivalence checks verifying that grammar optimizations preserve behavior:

```
Check 1: (parse_add ; parse_zero)  equiv?  parse_identity
Check 2: (parse_neg ; parse_neg)   equiv?  parse_skip
```

If adding zero is equivalent to identity but double negation is NOT equivalent to skip (because the grammar does not enforce the involution axiom):

### Output

```
note[K02] (OptLang): KAT equivalence: (parse_add ; [zero]) equiv (parse_identity)

note[K02] (OptLang): KAT equivalence: (parse_neg ; parse_neg) not equiv (1)
```

## Resolution

No action is strictly required, since K02 is informational. However, the results inform grammar design decisions:

**When equivalence is confirmed:**
- The grammar transformation is semantics-preserving. The optimization is safe to apply.
- This provides confidence for refactoring: the new grammar produces the same parse behavior.

**When inequivalence is detected:**
- If equivalence was expected, investigate the distinguishing guarded string. The asymmetric difference `L(e_1) symmetric_difference L(e_2)` contains at least one witness.
- Common causes of unexpected inequivalence:
  - Missing axioms (e.g., the grammar does not enforce `neg(neg(x)) = x`).
  - Different handling of edge cases (e.g., one expression handles empty input, the other does not).
  - Distinct treatment of Boolean test interactions (e.g., one expression checks a guard that the other assumes implicitly).

## Related Lints

- [K01](K01-hoare-failure.md) -- Hoare triple failure. K01 is a special case of KAT equivalence where one expression is zero: `{p} e {q}` is valid iff `test(p) . e . test(not q) equiv 0`. K02 handles the general case.
- [L01](../temporal/L01-ltl-violated.md) -- LTL property violation. K02 checks finite-trace behavioral equivalence; L01 checks infinite-trace temporal properties. Together they provide complementary verification coverage.
- [M02](../morphism/M02-morphism-preservation-failure.md) -- Morphism preservation failure. When a morphism maps a KAT expression `e` to `phi(e)`, K02 can verify that `e equiv phi(e)`.
- [P06](../P06-analysis-pipeline-cost.md) -- Reports total analysis phase time, which includes KAT analysis when the feature is enabled.
