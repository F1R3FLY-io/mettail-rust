# M02: morphism-preservation-failure

**Severity:** Warning
**Category:** analysis/morphism
**Feature Gate:** `morphisms`

## Description

A theory morphism `phi: T_1 -> T_2` must not only map every sort and operation (checked by M01) but also preserve every axiom of the source theory. Axiom preservation means that if `T_1` asserts an equation `s = t`, then `T_2` must satisfy `phi(s) = phi(t)`. M02 fires when an axiom of the source theory is not preserved under the morphism -- the translated equation does not hold in the target theory.

This is a semantic correctness property, as opposed to M01's structural completeness check. A morphism that passes M01 (no gaps) may still fail M02 if the target theory's operations do not respect the source theory's equations.

### Axiom Preservation Check

Given a source theory axiom `forall x_1, ..., x_n. lhs(x_1, ..., x_n) = rhs(x_1, ..., x_n)`, the morphism `phi` preserves this axiom iff:

```
forall y_1, ..., y_n.
    phi(lhs)(y_1, ..., y_n) = phi(rhs)(y_1, ..., y_n)
```

holds in the target theory `T_2`, where `phi(lhs)` denotes the term obtained by replacing every operation symbol `f` in `lhs` with its image `phi(f)`.

The check is performed by:

1. **Translating both sides.** Apply the morphism to every operation and sort reference in the equation.
2. **Normalizing in the target theory.** Reduce both translated sides using `T_2`'s axioms and rewrite rules.
3. **Comparing normal forms.** If the normal forms differ, the axiom is not preserved.

```
  Source axiom: lhs = rhs  (in T_1)
       |               |
  phi  |          phi  |
       v               v
  phi(lhs)         phi(rhs)
       |               |
  T_2  |          T_2  |
  norm |          norm |
       v               v
  nf(phi(lhs))    nf(phi(rhs))
       |               |
       └──── = ? ──────┘
            |
       ┌────┴────┐
       |         |
       v         v
     Equal    Not Equal
       |         |
       v         v
   Preserved  FAILURE
              (M02 fires)
```

### PraTTaIL Grammar Equations

In PraTTaIL, equations arise from:

- **Associativity axioms:** `(a + b) + c = a + (b + c)` for left-associative operators.
- **Commutativity axioms:** `a + b = b + a` for commutative operators.
- **Identity axioms:** `a + 0 = a`, `a * 1 = a` for operators with identity elements.
- **Cancellation pairs:** `Outer(Inner(x)) = x` for cast pairs that cancel.
- **Desugaring equations:** `if a then b else c = match a { true => b, false => c }`.

A morphism between grammars must preserve all such equations. For example, if the source grammar declares `+` as commutative and the morphism maps `+` to an operation in the target that is NOT commutative, M02 fires on the commutativity axiom.

## Trigger Conditions

M02 fires once per preservation failure. Specifically:

- The `morphisms` feature gate is enabled.
- The pipeline has computed a `MorphismAnalysis` result.
- The `preservation_failures` field contains at least one entry (a string describing the unpresented equation).
- One M02 diagnostic is emitted per failure.

If all axioms are preserved, M02 is silent.

## Example

### Grammar

Source grammar with commutative addition:

```
language! {
    name: CommLang;
    primary: Expr;

    category Expr {
        native_type: Integer;
        Num   = <int>;
        Add   = Expr "+" Expr;    // axiom: Add(a,b) = Add(b,a)
        Sub   = Expr "-" Expr;
    }
}
```

Target grammar where `Add` maps to a non-commutative `Concat`:

```
language! {
    name: SeqLang;
    primary: SeqExpr;

    category SeqExpr {
        native_type: String;
        Lit     = <string>;
        Concat  = SeqExpr "++" SeqExpr;   // NOT commutative!
        Drop    = SeqExpr "--" SeqExpr;
    }
}
```

Morphism: `Expr -> SeqExpr`, `Num -> Lit`, `Add -> Concat`, `Sub -> Drop`.

The commutativity axiom `Add(a, b) = Add(b, a)` translates to `Concat(a, b) = Concat(b, a)`, which does NOT hold for string concatenation.

### Output

```
warning[M02] (CommLang): equation not preserved under morphism: Add(a, b) = Add(b, a)
  = hint: the morphism does not preserve this algebraic equation
```

## Resolution

1. **Fix the target theory.** Make the target operation satisfy the required axiom. If `Concat` should be commutative in the target grammar, restructure the grammar to enforce it (e.g., normalize operand order).

2. **Weaken the source axiom.** If the commutativity axiom is not essential, remove it from the source theory. This makes the morphism preservation check succeed trivially for that axiom.

3. **Change the morphism mapping.** Map the source operation to a different target operation that does preserve the axiom. For example, map `Add` to a target operation that is commutative.

4. **Add a quotient.** Declare the equation as a quotient in the target theory, so that `Concat(a, b)` and `Concat(b, a)` are identified. This makes the normal forms equal.

## Hint Explanation

> the morphism does not preserve this algebraic equation

The hint identifies the nature of the failure: the morphism is structurally complete (every operation has an image) but semantically incorrect (not all equations transfer). The equation shown in the message is the specific axiom that fails. The grammar author should examine whether the target operation genuinely lacks the required property, or whether the morphism mapping is incorrect.

## Related Lints

- [M01](M01-morphism-gap.md) -- Structural gap detection. M01 must be resolved before M02 is meaningful: you cannot check axiom preservation for operations that have no target image. If both M01 and M02 fire, address M01 first.
- [G25](../../grammar/G01-left-recursion.md) -- Cancellation pair detection. Cancellation equations `Outer(Inner(x)) = x` are a common source of axioms that morphisms must preserve.
- [P06](../P06-analysis-pipeline-cost.md) -- Reports total analysis phase time, which includes morphism verification when the feature is enabled.
