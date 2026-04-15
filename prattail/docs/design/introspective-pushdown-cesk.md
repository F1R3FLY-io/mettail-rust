# Introspective Pushdown CESK: Evaluation WPDS + Abstract GC Fusion

## §1 The Problem

Pushdown analysis provides precise call/return matching but only accesses the stack **top**. Garbage collection needs the **full stack** (to compute root sets). Combining both naively breaks decidability.

## §2 Introspective Pushdown Systems

An **introspective pushdown system** (Earl et al., 2013) extends standard pushdown systems with read-only access to the full stack contents:

```
δ: Q × Γ × Γ* → P(Q × Γ*)
```

The key insight: read-only full-stack access preserves decidability as long as the transition function is **monotone** with respect to stack extensions (if a transition fires with stack `w`, it also fires with stack `w·w'`).

PraTTaIL's `CekObserver` callback already provides introspective access — it can read the full continuation stack at each transition point.

## §3 Evaluation WPDS Construction

The evaluation WPDS models the CESK machine:

- **Control states**: `(Exp × Env_hat × Store_hat)` — abstracted expression + environment + store
- **Stack alphabet**: `EvalStackSymbol` variants (BinOp, LetBody, SetCont, Parallel, ...)
- **Transition rules**: Derived from CESK transition function

```
⟨(let x=e₁ in e₂), ρ, σ⟩ --push(LetBody{x})-→ ⟨e₁, ρ, σ⟩
⟨v, ρ, σ⟩ --pop(LetBody{x})-→ ⟨e₂, ρ[x↦a], σ[a↦v]⟩
```

## §4 Dyck State Graphs

A Dyck State Graph (DSG) compactly represents all reachable configurations of the evaluation pushdown system. Construction is iterative:

```
1. Initialize DSG with initial configuration
2. For each unexpanded node:
   a. Compute successors via abstract CESK transition
   b. Add edges (push/pop labeled with stack symbols)
   c. Mark node as expanded
3. Repeat until fixpoint (no new nodes)
```

The resulting graph has `O(|Exp| × |Env_hat| × |Store_hat|)` nodes — finite when using abstract allocation.

## §5 Fusion: Pushdown + Abstract GC

**Abstract GC** uses introspective stack access to compute `LL_σ(e, ρ, κ)`:
- Root set: addresses in `ρ` + addresses in all frames of `κ`
- Transitive closure through store (follow closure captures)
- Remove unreachable abstract cells

**Synergy** (Earl et al., Figure 2): With abstract GC, 0CFA on a benchmark went from 653 states to 77 states. The combined analysis is more precise than either alone:
- GC removes spurious flows (dead closures don't pollute the store)
- Pushdown removes spurious returns (matched call/return prevents impossible paths)

## §6 Static Analysis Queries

Given a constructed DSG:
- "Can closure `f` flow to call site `s`?" → BFS reachability in DSG
- "Is variable `x` live at point `p`?" → introspective stack inspection at DSG nodes containing `p`
- "What are the possible values of `x` at point `p`?" → collect `store[env[x]]` across all DSG nodes containing `p`

## Implementation

- `prattail/src/abstract_cesk.rs`: `AbstractStore`, `abstract_gc()`, `DyckStateGraph`, `is_reachable()`
- Integration with Ascent: DSG construction encodable as Ascent relations for fixpoint computation

## References

- Earl, C., Sergey, I., Johnson, J. I., Might, M. & Van Horn, D. (2013). Introspective Pushdown Analysis. *J. Functional Programming*.
- Bouajjani, A., Esparza, J. & Maler, O. (1997). Reachability analysis of pushdown automata.
- Reps, T., Schwoon, S., Jha, S. & Melski, D. (2005). Weighted pushdown systems and their application to interprocedural dataflow analysis.
