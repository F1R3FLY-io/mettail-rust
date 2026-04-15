# Continuation Stack Architecture

## Defunctionalization

The `Frame_Cat` enum is a **defunctionalization** (Reynolds, 1972) of continuation closures. Each frame variant is a tagged record that captures the free variables of the continuation closure; the unwind handler is the apply function that reconstructs the closure's computation.

### Correspondence

| Continuation Closure | Frame Variant | Unwind Handler |
|---------------------|---------------|---------------|
| `λ rhs. (Add(lhs, rhs), bp)` | `InfixRHS { lhs, op_pos, saved_bp }` | `lhs = make_infix(tokens[op_pos], lhs, rhs); cur_bp = saved_bp;` |
| `λ v. (Neg(v), bp)` | `UnaryPrefix_Neg { saved_bp }` | `lhs = Cat::Neg(Box::new(lhs)); cur_bp = saved_bp;` |
| `λ nt. cont(captures, nt)` | `RD_L_i { saved_bp, c₁, …, cₖ }` | Process next segment or construct AST |

### Correctness (Theorem CEK.5)

Each unwind handler exactly reproduces the continuation closure's computation. This is proved by showing that for any frame `F` with captured values `(v₁, …, vₖ)` and parsed result `r`:

```
apply_closure(defunctionalize⁻¹(F), r) = unwind_handler(F, r)
```

See `formal/rocq/trampoline/theories/Defunctionalization.v`.

## Thread-Local Pooling

The continuation stack uses `Cell<Vec<Frame_Cat>>` for zero-allocation pooling:

```
Thread-Local:  FRAME_POOL_Cat: Cell<Vec<Frame_Cat>>

parse_Cat():
  stack = FRAME_POOL_Cat.take()    // Takes Vec, leaves empty Vec in Cell
  result = parse_Cat_impl(&mut stack)
  FRAME_POOL_Cat.set(stack)         // Returns Vec for reuse
  return result
```

### Re-Entrancy

When `parse_Cat()` is called recursively (e.g., cross-category calls):
1. Outer call takes the pooled Vec
2. Inner call finds the Cell empty → allocates fresh Vec
3. Inner call completes → sets its Vec back
4. Outer call completes → sets its Vec back (overwrites inner's)

Only one Vec is pooled per thread per category. The key invariant: the most recent `set()` wins.

### Capacity Hint (RT-01)

WPDS depth bounds (G34) provide a pre-computed hint for the pool capacity:

```rust
thread_local! {
    static FRAME_POOL_Cat: Cell<Vec<Frame_Cat>> =
        Cell::new(Vec::with_capacity(/* G34 depth bound */));
}
```

## CoW Stacks (Future: `im::Vector`)

For incremental parsing with token-level checkpoints, consecutive checkpoints typically differ only in the top frame. Using persistent data structures:

```rust
type PersistentStack<Frame> = im::Vector<Frame>;
```

- O(log n) push/pop
- O(1) clone via structural sharing (RRB trees)
- Memory overhead per checkpoint: O(log n) instead of O(n)

Feature-gated under `reactive-cek`.

## References

- Reynolds, J. C. (1972). *Definitional interpreters for higher-order programming languages.* ACM Annual Conference.
- Danvy, O. & Nielsen, L. R. (2003). *Defunctionalization at work.* PPDP.
