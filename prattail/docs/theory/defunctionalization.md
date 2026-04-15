# Defunctionalization Correctness

## Theorem (CEK.5)

The `Frame_Cat` enum is a correct defunctionalization (Reynolds, 1972) of continuation closures. Each unwind handler exactly reproduces the closure's computation.

## Background

**Defunctionalization** is a program transformation that replaces first-class functions with tagged records. Each function is assigned a unique tag; the tag plus the function's free variables form the record. An `apply` function dispatches on the tag.

In PraTTaIL's trampoline:
- **Tags**: Frame variant names (`InfixRHS`, `UnaryPrefix_Neg`, `RD_Let_0`, etc.)
- **Free variables**: Frame fields (`lhs`, `op_pos`, `saved_bp`, etc.)
- **Apply function**: The unwind `match` in the `'unwind` loop

## Formal Statement

For any continuation `k : Cat → (Cat, u8)` that arises during parsing:

```
∃! tag, fields. defunctionalize(k) = Frame_Cat::tag { fields }
```

and for all values `v : Cat`:

```
k(v) = unwind_handler(Frame_Cat::tag { fields }, v)
```

## Proof Structure

1. **Enumerate all continuation forms**: By exhaustive analysis of the trampoline codegen, there are exactly 9 classes of continuations (InfixRHS, GroupClose, UnaryPrefix, RD, CollectionElem, Mixfix, LambdaBody, Dollar, GuardEval).

2. **For each class, show the bijection**: The frame variant captures exactly the continuation's free variables, and the unwind handler reproduces the closure body.

3. **Show uniqueness**: Each continuation form maps to exactly one frame variant (no aliasing).

## Example: InfixRHS

### Continuation
```
k = λ rhs. (make_infix(tokens[op_pos], lhs, rhs), saved_bp)
```
Free variables: `lhs`, `op_pos`, `saved_bp`.

### Defunctionalized Frame
```rust
Frame_Cat::InfixRHS { lhs: Cat, op_pos: usize, saved_bp: u8 }
```

### Unwind Handler
```rust
Some(Frame_Cat::InfixRHS { lhs: prev, op_pos, saved_bp }) => {
    lhs = make_infix(&tokens[op_pos].0, prev, lhs);
    cur_bp = saved_bp;
}
```

### Verification
```
k(rhs) = (make_infix(tokens[op_pos], lhs, rhs), saved_bp)
       = unwind_handler(InfixRHS { lhs, op_pos, saved_bp }, rhs)  ✓
```

## Relationship to CEK.1

Theorem CEK.5 refines CEK.1 (Trampoline/Recursion Equivalence) by showing that the defunctionalization step preserves the continuation semantics exactly. CEK.1 shows the outer equivalence; CEK.5 explains the mechanism.

## Formal Proof

Machine-checked in `formal/rocq/trampoline/theories/Defunctionalization.v`.

## References

- Reynolds, J. C. (1972). *Definitional interpreters for higher-order programming languages.* ACM Annual Conference.
- Danvy, O. & Nielsen, L. R. (2003). *Defunctionalization at work.* PPDP.
- Pottier, F. & Gauthier, N. (2006). *Polymorphic typed defunctionalization and concretization.* HOSC.
