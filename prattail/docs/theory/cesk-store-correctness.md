# CESK Store Correctness: Formal Properties

## §1 Store Invariants

### Alloc Monotonicity
For any store σ and value v:
```
alloc(σ, v) = (a, σ')  ⟹  a = max(dom(σ)) + 1
```
Addresses are never reused. This simplifies GC epoch-based TOCTOU prevention.

**Rocq proof**: `CeskStoreCorrectness.alloc_monotonicity`

### Get-After-Set
For any store σ, address a ∈ dom(σ), and value v:
```
get(set(σ, a, v), a) = Some(v)
```

**Rocq proof**: `CeskStoreCorrectness.get_after_set_same`

### Non-Interference
For any store σ, addresses a ≠ a', and value v:
```
get(set(σ, a, v), a') = get(σ, a')
```
Setting at one address does not affect any other address.

**Rocq proof**: `CeskStoreCorrectness.set_non_interference`

## §2 Two-Stage Equivalence Theorem

For **immutable bindings** (no `set!` between `bind` and `lookup`), the CESK machine is equivalent to the CEK machine:

```
∀ x, v, ρ, σ:
  let (a, σ') = alloc(σ, v) in
  let ρ' = ρ[x ↦ a] in
  σ'(ρ'(x)) = v = ρ_direct(x)
```

The indirection through the store adds no observable difference for purely functional evaluation. This guarantees backward compatibility with existing CEK-based evaluations.

**Rocq proof**: `CeskStoreCorrectness.bind_resolve_equivalence`

## §3 Fork Isolation Theorem

For persistent stores with structural sharing:
```
∀ σ, a, v:
  let child = fork(σ) in
  let child' = set(child, a, v) in
  get(σ, a) = get(σ_original, a)   — parent unchanged
```

Mutations in a forked child store do not affect the parent, despite sharing internal tree nodes. This is a consequence of `im::HashMap`'s copy-on-write semantics.

**Rocq proof**: `CeskMutation.fork_isolation`

## §4 GC Soundness

Mark-sweep collects exactly the unreachable addresses:

```
∀ roots, refs, a:
  ¬reachable(roots, refs, a)  ⟺  is_dead(roots, refs, a)
```

No live address is ever collected (safety). Every dead address is collected (completeness).

**Rocq proofs**: `CeskMutation.gc_soundness`, `CeskMutation.gc_completeness`, `CeskMutation.gc_preserves_live`

## §5 Refcount Safety

`dec_ref` only signals death when the count transitions from 1 to 0:
```
snd(dec_ref(rc, a)) = true  ⟺  get_count(rc, a) = 1
```

**Rocq proof**: `CeskStoreCorrectness.dec_ref_dead_iff_count_one`

## §6 Mutation Locality

Setting a store cell only affects that cell:
```
∀ σ, a, a', v:  a ≠ a'  ⟹  get(set(σ, a, v), a') = get(σ, a')
```

This is the formal basis for aliasing: two variables at the same address see each other's mutations, but variables at different addresses are isolated.

**Rocq proof**: `CeskMutation.mutation_locality`

## §7 Proof Index

| Property | File | Status |
|----------|------|--------|
| Alloc monotonicity | CeskStoreCorrectness.v | Proved |
| Get-after-set | CeskStoreCorrectness.v | Proved |
| Non-interference | CeskStoreCorrectness.v | Proved |
| Remove correctness | CeskStoreCorrectness.v | Proved |
| Refcount roundtrip | CeskStoreCorrectness.v | Proved |
| Refcount dead iff count=1 | CeskStoreCorrectness.v | Proved |
| n inc / n dec = 0 | CeskStoreCorrectness.v | Proved |
| Two-stage equivalence | CeskStoreCorrectness.v | Proved |
| Mutation locality | CeskMutation.v | Proved |
| Mutation visibility | CeskMutation.v | Proved |
| Fork isolation | CeskMutation.v | Proved |
| Fork content equality | CeskMutation.v | Proved |
| GC soundness | CeskMutation.v | Proved |
| GC completeness | CeskMutation.v | Proved |
| GC preserves live | CeskMutation.v | Proved |
| Reachability monotone | CeskMutation.v | Proved |
