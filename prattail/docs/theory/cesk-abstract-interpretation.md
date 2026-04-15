# CESK Abstract Interpretation: Machines as Analyzers

## §1 The AAM Recipe

Van Horn & Might's "Abstracting Abstract Machines" (ICFP 2010) provides a systematic recipe for deriving abstract interpreters from concrete machines:

1. **Start with a concrete machine** (CESK with MonotonicAlloc)
2. **Replace `alloc`** with an abstract strategy (0CFA, k-CFA)
3. **Widen the store** to map addresses to sets of values (join)
4. **Compute fixpoint** over the finite abstract state space

The result is a sound abstract interpreter: every behavior of the concrete machine is captured (approximated) by the abstract machine.

## §2 Structural Abstraction via Store

The key insight: the store makes environments and continuations **non-recursive**. In a direct (storeless) machine, closures contain environments that contain closures (recursive structure → infinite states). With a store:

```
Closure = (body, env)       where env : Var → Addr
```

The closure no longer contains values — it contains addresses. Values are in the store. This breaks the recursion.

## §3 Soundness

**Theorem** (AAM Theorem 4.1): If `α` is the abstraction function:

```
α(concrete_state) ⊑ abstract_state
```

then for every concrete transition `c → c'`, there exists an abstract transition `â → â'` such that `α(c') ⊑ â'`.

In other words: the abstract machine simulates every concrete execution path (it may also admit spurious paths, but it never misses a real one).

## §4 Decidability

- **Finite address space** (abstract alloc returns from a finite set)
- → **Finite store** (each address has finitely many abstract values)
- → **Finite state space** (Exp × Env_hat × Store_hat × Kont_hat is bounded)
- → **Decidable reachability** (BFS/DFS on finite transition graph)
- → **Computable fixpoint** (Ascent iteration terminates)

## §5 Connection to Ascent

PraTTaIL's Ascent fixpoint engine is a natural target for abstract CESK analysis:

```datalog
% Abstract CESK states as Ascent relations
reachable(e, env_fp, store_fp) :- initial_config(e, env_fp, store_fp).
reachable(e', env', store') :-
    reachable(e, env, store),
    abstract_step(e, env, store, e', env', store').

% Flow queries
may_flow(call_site, closure) :-
    reachable(call_site, env, store),
    abstract_apply(call_site, env, store, closure).
```

The Ascent engine handles fixpoint iteration, stratification, and incremental updates. Abstract CESK analysis becomes a set of Datalog rules.

## References

- Van Horn, D. & Might, M. (2010). Abstracting Abstract Machines. *ICFP 2010*.
- Might, M. (2007). Environment analysis of higher-order languages. PhD thesis.
- Earl, C. et al. (2013). Introspective Pushdown Analysis. *JFP*.
