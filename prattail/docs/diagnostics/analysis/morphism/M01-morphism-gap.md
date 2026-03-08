# M01: morphism-gap

**Severity:** Warning
**Category:** analysis/morphism
**Feature Gate:** `morphisms`

## Description

A theory morphism `phi: T_1 -> T_2` is a structure-preserving map between two formal theories. For the morphism to be well-defined, every sort and operation in the source theory `T_1` must have an image in the target theory `T_2`. M01 fires when the morphism analysis detects a gap -- an operation (constructor) in the source theory that has no corresponding mapping in the target theory.

In the PraTTaIL context, theories correspond to grammar categories and their rules. A morphism between two grammars (or two versions of the same grammar) maps categories to categories and rules to rules. A gap means that a source grammar constructor has no counterpart in the target grammar, making the morphism incomplete.

### Morphism Commutation Diagram

A complete theory morphism must make the following diagram commute for every operation `f` in the source theory:

```
     Source Theory T_1                    Target Theory T_2

  Sort_1(T_1) x ... x Sort_n(T_1)   phi_sorts   Sort_1(T_2) x ... x Sort_n(T_2)
            |                        -------->              |
            |                                               |
     f_T1   |                                        f_T2   |
            |                                               |
            v                        phi_sorts              v
       Sort_r(T_1)               -------->            Sort_r(T_2)
```

The commutation requirement states:

```
phi_sorts(f_T1(a_1, ..., a_n)) = f_T2(phi_sorts(a_1), ..., phi_sorts(a_n))
```

For this equation to hold, `f_T2` must exist. When M01 fires, it means `f_T2` is missing: there is no operation in `T_2` to serve as the image of `f_T1`.

### Concretely for PraTTaIL Grammars

Consider a source grammar with categories `{Expr, Type}` and a target grammar with categories `{CoreExpr, CoreType}`. The morphism maps:

```
phi(Expr) = CoreExpr
phi(Type) = CoreType
```

Each rule in the source grammar must map to a rule in the target grammar:

```
phi(ExprAdd) = CoreAdd      -- OK
phi(ExprMul) = CoreMul      -- OK
phi(ExprPow) = ???           -- GAP! No CorePow exists
```

The gap for `ExprPow` means the morphism is incomplete: the source grammar supports exponentiation but the target grammar does not. Either the target needs a `CorePow` rule, or the morphism needs a desugaring step (e.g., `phi(ExprPow(a,b)) = CoreMul(a, CoreMul(a, ...))` for constant exponents).

## Trigger Conditions

M01 fires once per gap in the morphism. Specifically:

- The `morphisms` feature gate is enabled.
- The pipeline has computed a `MorphismAnalysis` result.
- The `gaps` field contains at least one entry (a string identifying the unmapped constructor).
- One M01 diagnostic is emitted per gap.

If the morphism is complete (no gaps), M01 is silent.

## Example

### Grammar

Source grammar:

```
language! {
    name: SourceLang;
    primary: Expr;

    category Expr {
        native_type: Integer;
        NumLit  = <int>;
        Add     = Expr "+" Expr;
        Pow     = Expr "^" Expr;     // exponentiation
    }
}
```

Target grammar:

```
language! {
    name: CoreLang;
    primary: CoreExpr;

    category CoreExpr {
        native_type: Integer;
        CoreNum = <int>;
        CoreAdd = CoreExpr "+" CoreExpr;
        // Note: no exponentiation rule
    }
}
```

Morphism specification: `Expr -> CoreExpr`, `NumLit -> CoreNum`, `Add -> CoreAdd`.

### Output

```
warning[M01] (SourceLang): theory morphism incomplete -- missing constructor mapping: Pow
  = hint: add a cross-category rule or constructor to complete the morphism
```

## Resolution

1. **Add the missing operation to the target theory.** The most direct resolution: define `CorePow = CoreExpr "^" CoreExpr` in the target grammar so the morphism can map `Pow -> CorePow`.

2. **Define a desugaring for the missing constructor.** If the target theory intentionally omits the operation, define the morphism's image as a composite expression. For example, `phi(Pow(a, 3)) = Mul(a, Mul(a, a))`. This requires extending the morphism definition beyond simple constructor-to-constructor mapping.

3. **Restrict the source theory.** If the operation is not needed in the source grammar, remove it. This eliminates the gap trivially.

4. **Add a cross-category rule.** In PraTTaIL, a cross-category rule from the source category to a target-compatible category can serve as the morphism's image for the missing constructor.

## Hint Explanation

> add a cross-category rule or constructor to complete the morphism

The hint identifies the two primary resolution paths: either add the missing constructor directly to the target theory (making the morphism total), or add a cross-category rule that provides a translation path for the missing operation. The morphism cannot be verified for axiom preservation (M02) until it is structurally complete.

## Related Lints

- [M02](M02-morphism-preservation-failure.md) -- Axiom preservation failure. M01 detects structural gaps (missing operations); M02 detects semantic gaps (operations exist but axioms are not preserved). M01 must be resolved before M02 can meaningfully fire on the affected operations.
- [G08](../../grammar/G08-missing-cast-to-root.md) -- Missing cast to root. A morphism gap is analogous to a missing cast: both represent incomplete connectivity in the grammar's structure.
- [P06](../P06-analysis-pipeline-cost.md) -- Reports total analysis phase time, which includes morphism analysis when the feature is enabled.
