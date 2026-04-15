# CESK Machine: Store-Extended Evaluation for MeTTaIL

## §1 Motivation: Why CEK → CESK

The CEK machine (Control, Environment, Kontinuation) maps variables directly to values:
```
env[x] = "42"
```

This is sufficient for purely functional evaluation but cannot express:

1. **Mutation (`set!`)**: Overwriting a variable's value after binding
2. **Aliasing**: Two variables sharing state (mutation through one visible through the other)
3. **Shared closures**: Closures that capture mutable references
4. **Channel semantics**: Rholang's tuplespace requires named channels with lifecycle management

The CESK machine (Felleisen, 1986) adds an explicit **Store** component that introduces address-based indirection:

```
env[x] → addr₁         (environment maps variables to addresses)
store[addr₁] → "42"    (store maps addresses to values)
```

### Side-by-Side: CEK vs CESK Lookup

```
CEK:   lookup(x, ρ)     = ρ(x)                    ← one step
CESK:  lookup(x, ρ, σ)  = σ(ρ(x))                 ← two steps (indirection)
```

The extra indirection enables mutation:
```
set!(x, "99"):
  addr = ρ(x)                    ← get the address (unchanged)
  σ' = σ[addr ↦ "99"]           ← overwrite the store cell
  — ρ is unchanged; any variable aliasing addr sees the new value
```

## §2 The CESK Machine: Formal Definition

### State Configuration

A CESK machine state is a 4-tuple:

```
ς ∈ Σ = Exp × Env × Store × Kont
```

where:
- **Exp**: Current expression (control term)
- **Env** = Var ⇀ Addr: Environment mapping variables to addresses
- **Store** = Addr ⇀ Storable: Store mapping addresses to values
- **Kont**: Continuation stack (evaluation context)

### Transition Rules

| Rule | From | To | Description |
|------|------|----|-------------|
| Reduce | `⟨e, ρ, σ, κ⟩` | `⟨e', ρ, σ, κ⟩` | Select rewrite rule |
| Descend | `⟨(f e₁), ρ, σ, κ⟩` | `⟨e₁, ρ, σ, (f □)::κ⟩` | Enter subterm |
| Ascend | `⟨v, ρ, σ, (f □)::κ⟩` | `⟨(f v), ρ, σ, κ⟩` | Return from subterm |
| Bind | `⟨(let x=v in e), ρ, σ, κ⟩` | `⟨e, ρ[x↦a], σ[a↦v], κ⟩` | Bind variable (a fresh) |
| Mutate | `⟨(set! x v), ρ, σ, κ⟩` | `⟨void, ρ, σ[ρ(x)↦v], κ⟩` | Mutate store cell |
| Accept | `⟨v, ρ, σ, []⟩` | terminal | Normal form reached |

### The `set!` Transition (Mutation)

```
⟨(set! x ae), ρ, σ, κ⟩  →  ⟨void, ρ, σ[ρ(x) ↦ A(ae, ρ, σ)], κ⟩
```

where `A(ae, ρ, σ)` evaluates the atomic expression `ae` in environment `ρ` with store `σ`.

Key properties:
- The **environment ρ is unchanged** — mutation doesn't rebind
- The **store cell σ[ρ(x)]** is overwritten in place
- Any variable `y` where `ρ(y) = ρ(x)` (aliased) sees the new value

## §3 Two-Tier Store Architecture

### Rationale

In the M:N green thread runtime, local bindings (let-bindings, closures) are thread-private, while channels and tuplespace entries are shared. A two-tier architecture separates these concerns:

```
┌────────────────────────────────────────────────────────────────────┐
│                    Global Store (Tier 2)                            │
│  DashMap<u64, StoreValue>  — lock-free, shared across all threads  │
│  Arc<AtomicU64> global_next_addr — monotonic allocation            │
│  • Channel refs (StoreValue::ChannelRef(ChannelId))                │
│  • Names created by `new` (shared across P | Q)                    │
│  • GC: async mark-and-sweep (snapshot at coordinator idle)         │
├──────────────────────────┬─────────────────────────────────────────┤
│     Green Thread 0       │      Green Thread 1                     │
│  ┌────────────────────┐  │  ┌────────────────────┐                 │
│  │ Local Store (Tier 1)│  │  │ Local Store (Tier 1)│                │
│  │ im::HashMap (CoW)  │  │  │ im::HashMap (CoW)  │                │
│  │ • let bindings      │  │  │ • let bindings      │                │
│  │ • pattern match     │  │  │ • pattern match     │                │
│  │ • closure envs      │  │  │ • closure envs      │                │
│  └────────────────────┘  │  └────────────────────┘                 │
└──────────────────────────┴─────────────────────────────────────────┘
```

### StoreAddr: Tagged Dispatch

```rust
pub enum StoreAddr {
    Local(u64),   // → per-thread im::HashMap
    Global(u64),  // → shared DashMap
}
```

Lookup dispatches on the variant: `Local` goes to the owning thread's persistent store, `Global` goes to the shared DashMap.

### O(1) Fork via Persistent Store

When a Rholang process forks (`P | Q`), the child receives a structural-sharing clone of the parent's local store via `im::HashMap::clone()`. This is O(1) — only Arc reference counts are bumped. Subsequent mutations on either parent or child diverge via copy-on-write at the affected HAMT nodes.

## §4 Store Values

```rust
pub enum StoreValue {
    Simple(String),                              // Scalars, strings
    Closure { env_snapshot, body },              // Functions with captured env
    ChannelRef(ChannelId),                       // Channel lifecycle tracking
    Void,                                        // Unit value (set! result)
    Relation { name, tuples },                   // Ascent-derived relations
    Constraint { domain, predicate, bindings },  // Refinement type constraints
    RewriteRule { name, lhs, rhs, priority },    // First-class rewrite rules
    EClass { class_id, members, cost_leader },   // E-graph equivalence classes
}
```

## §5 Channel Bridge (Hybrid Lifecycle)

```
env["ch"] → StoreAddr::Global(42) → global_store[42] = ChannelRef(ch_id_7)
                                                              │
                                     ChannelMap.get(ch_id_7) ─┘
                                           │
                                     crossbeam Sender/Receiver
```

- **Store** tracks channel **lifecycle** (reference counting via GC)
- **ChannelMap** handles **transport** (lock-free MPMC via crossbeam)
- When the last `ChannelRef` is GC'd → `ChannelMap.dec_ref(ch_id)` → channel removed

## §6 Garbage Collection

### §6.1 Strategy Configuration

| Strategy | Overhead | Cycle Detection | Best For |
|----------|----------|-----------------|----------|
| `None` | Zero | N/A | Short evals, step-limited |
| `RefCount` | Low | No | Lambda calculus, closures |
| `MarkSweep` | Medium | Yes | Rho-calculus, channels |

### §6.2 Reference Counting

```
bind(x, v):    addr = alloc(v); env[x] = addr; inc_ref(addr)
unbind(x):     dec_ref(env[x]); env.remove(x)
dec_ref(addr): count--; if count == 0: enqueue(dead_addrs)
```

Dead addresses are processed **asynchronously**: pushed to a lock-free queue, drained in batches by a background thread, applied at quantum boundaries (GC safe points).

### §6.3 Mark-and-Sweep

The `LL_σ` live locations function (Van Horn & Might, AAM §4, Figure 7):

```
LL_σ(e, ρ) = LL_σ(ρ|fv(e))
LL_σ(ρ)    = rng(ρ)
LL_σ(clo(v, ρ, a)) = {a} ∪ LL_σ(v, ρ) ∪ LL_σ(σ(a))
```

Protocol:
1. **Snapshot** at coordinator idle (all threads yielded)
2. **Mark** via iterative worklist from roots (no recursion)
3. **Sweep** unreachable addresses
4. **Epoch filtering**: addrs allocated after snapshot are exempt (TOCTOU prevention)

### §6.4 Adaptive Quantum Sizing (Backpressure)

| Tier | Quantum | Trigger |
|------|---------|---------|
| Normal | 1000 steps | Default |
| Light | 750 steps | Alloc rate > 50% threshold |
| Medium | 500 steps | Alloc rate > 75% threshold |
| Heavy | 250 steps | Committed bytes > GC threshold |

Higher pressure → smaller quanta → more frequent yields → more GC safe points.

## §7 Parameterized Allocation (AAM Recipe)

The CESK*_t machine parameterizes allocation by:
- `tick(Σ) → Time` — advances machine time
- `alloc(Var, Σ) → Addr` — chooses addresses from computation state

| Analysis | Addr | alloc(v, ĉ) |
|----------|------|-------------|
| Concrete | u64 | Monotonic counter |
| 0CFA | hash(Var) | Monovariant |
| 1CFA | hash(Var, Exp) | Context-sensitive |
| k-CFA | hash(Var, Exp^k) | Last k expressions |

Swapping `MonotonicAlloc` for `ZeroCfaAlloc` makes the state space finite, enabling static analysis via fixpoint computation through the existing Ascent engine.

## §8 Abstract GC + Introspective Pushdown

The abstract CESK machine's store maps addresses to **sets** of values (due to address reuse). Abstract GC removes unreachable abstract cells, preventing spurious flow accumulation.

The evaluation WPDS models the CESK machine as a pushdown system. Combined with abstract GC (Earl et al., 2013), this yields "better than both worlds" precision: GC removes spurious flows, pushdown removes spurious returns.

The Dyck State Graph provides a compact representation of all reachable evaluation configurations, enabling queries like "Can closure f flow to call site s?"

## References

- Felleisen, M. & Friedman, D. P. (1986). Control operators, the SECD-machine, and the λ-calculus.
- Van Horn, D. & Might, M. (2010). Abstracting Abstract Machines. *ICFP 2010*.
- Earl, C. et al. (2013). Introspective Pushdown Analysis. *JFP*.
- Might, M. CESK machines tutorial. https://matt.might.net/articles/cesk-machines/
