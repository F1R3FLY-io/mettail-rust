# Parameterized Allocation: The AAM Recipe

## §1 Motivation

The same CESK machine serves dual purpose:
- **Concrete execution**: `MonotonicAlloc` — infinite addresses, every binding unique
- **Static analysis**: `ZeroCfaAlloc` / `KCfaAlloc` — finite addresses, fixpoint computation

The `AllocStrategy` trait is the knob that tunes this duality.

## §2 The AllocStrategy Trait

```rust
pub trait AllocStrategy: Send + Sync + Debug {
    fn tick(&self, config: &CeskConfig) {}
    fn alloc(&self, var: &str, config: &CeskConfig) -> u64;
    fn name(&self) -> &'static str;
}
```

- `tick(Σ)`: Advance the time component (history of computation)
- `alloc(v, Σ)`: Choose an address for variable `v` given machine state `Σ`

## §3 Concrete Allocation: MonotonicAlloc

```
alloc(v, Σ) = next++    (monotonic counter, O(1) atomic)
```

Every binding gets a fresh, unique address. The address space is infinite (u64). This is the default for concrete execution — identical behavior to the pre-CESK evaluator.

## §4 Abstract Allocation Strategies

### 0CFA (Monovariant)

```
Addr = hash(Var)
alloc(v, _) = hash(v)
```

Every binding of the same variable name gets the same address. The store accumulates all values ever bound to that variable: `σ[hash("x")] = {v₁, v₂, ...}`. State space: |Var| × |Value|^|Var| — finite when values are abstracted.

### 1CFA (Context-Sensitive)

```
Addr = hash(Var, Exp)
alloc(v, ĉ) = hash(v, ĉ.control)
```

Different call sites produce different addresses for the same variable. Distinguishes `f(1)` from `f(2)` when `f` binds parameter `x`.

### k-CFA

```
Addr = hash(Var, Exp^k)
alloc(v, ĉ) = hash(v, ⟨e₁,...,eₖ⟩)
```

Generalizes 1CFA with the last `k` expressions as context. Higher k = more precision but exponentially larger state space. In practice, k=1 suffices for most analyses.

## §5 How Abstract Interpretation Emerges

1. **Finite address space** → finite store → finite state space
2. **Finite state space** → the transition system is a finite graph
3. **Finite graph** → reachability is decidable → fixpoint computable
4. **Fixpoint** → sound approximation of all possible concrete executions

This connects directly to PraTTaIL's Ascent fixpoint engine: the abstract CESK machine's states become Ascent relations, and fixpoint iteration computes the analysis.

## §6 Integration with Ascent

```
reachable_config(expr, env_fp, store_fp) :- /* initial config */;
reachable_config(e', env', store') :-
    reachable_config(e, env, store),
    cesk_step(e, env, store, e', env', store');
```

The `cesk_step` relation encodes the CESK transition function. Ascent computes the fixpoint (all reachable abstract configurations) in O(|states|²) time.

## References

- Van Horn, D. & Might, M. (2010). Abstracting Abstract Machines. *ICFP 2010*, §2.4.
- Might, M. (2007). Environment analysis of higher-order languages. PhD thesis.
- Shivers, O. (1991). Control-flow analysis of higher-order languages. PhD thesis.
