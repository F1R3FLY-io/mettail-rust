# Petri Nets / VASS -- Concurrent Process Analysis

| Property | Value |
|----------|-------|
| **Feature gate** | `petri` |
| **Source file** | `prattail/src/petri.rs` (~1731 lines) |
| **Pipeline phase** | Concurrency analysis |
| **Lint codes** | N01 (`deadlock-risk`), N02 (`unbounded-channel`) |

## 1. Rationale

PraTTaIL grammars with parallel composition operators (e.g., Rholang's `|`)
introduce concurrency. Detecting deadlocks, verifying bounded resource usage,
and identifying maximal parallelism require a formal concurrency model. Petri
nets provide exactly this: places model communication channels, transitions model
process actions, and tokens model available messages. The Karp-Miller coverability
tree gives decidable answers to coverability and boundedness, while deadlock
detection identifies stuck configurations.

## 2. Theoretical Foundations

### 2.1. Petri Net Definition

**Definition (Petri Net).** A Petri net is a tuple `N = (P, T, F, W, m_0)` where:

- `P` is a finite set of **places**
- `T` is a finite set of **transitions** (P and T are disjoint)
- `F subseteq (P x T) cup (T x P)` is the **flow relation**
- `W: F -> N^+` is the **weight function** on arcs
- `m_0: P -> N` is the **initial marking**

**Definition (Marking).** A marking `m: P -> N` assigns a non-negative integer
(token count) to each place. A marking is a vector in `N^|P|`.

**Definition (Enabled Transition).** Transition `t` is **enabled** at marking `m`
iff for all `p in pre(t)`: `m(p) >= W(p, t)`, where `pre(t) = {p | (p,t) in F}`.

**Definition (Firing).** Firing enabled transition `t` at marking `m` produces
marking `m'`:

```
m'(p) = m(p) - W(p, t) + W(t, p)    for all p in P
```

### 2.2. Decision Problems

**Theorem (Coverability; Karp & Miller 1969).** The coverability problem for
Petri nets is decidable. Given a Petri net `N` with initial marking `m_0` and a
target marking `m`, it is decidable whether there exists a reachable marking
`m'` such that `m' >= m` (component-wise).

The Karp-Miller algorithm constructs a **coverability tree** where nodes are
generalized markings (using `omega` to denote unbounded places). The tree is
finite because generalized markings with `omega` components subsume infinitely
many concrete markings.

**Theorem (Boundedness).** A Petri net is **bounded** iff no node in the
Karp-Miller tree contains `omega`. A place `p` is **k-bounded** iff
`m(p) <= k` for all reachable markings `m`.

**Theorem (Deadlock Detection).** A marking `m` is a **deadlock** iff no
transition is enabled at `m`. Deadlock detection reduces to checking whether
the reachable state space contains a deadlock marking.

### 2.3. Independence and Parallelism

**Definition (Independence).** Transitions `t1` and `t2` are **independent** iff:

```
(pre(t1) cup post(t1)) cap (pre(t2) cup post(t2)) = emptyset
```

Independent transitions can fire concurrently without interfering.

**Definition (Parallel Region).** A parallel region is a maximal clique in the
independence graph: every pair of transitions in the region is independent.

## 3. Algorithm Pseudocode

### 3.1. Karp-Miller Coverability Tree

```
function karp_miller(net: PetriNet, initial: Marking) -> CoverabilityTree:
    root := TreeNode(initial)
    worklist := Queue
    worklist.push(root)

    while node := worklist.pop():
        m := node.marking
        for each transition t enabled at m:
            m' := fire(t, m)

            // Acceleration: check if m' strictly covers an ancestor
            ancestor := node
            while ancestor != null:
                if m' > ancestor.marking:
                    // Set unbounded (omega) for places where m'(p) > ancestor(p)
                    for p where m'(p) > ancestor.marking(p):
                        m'(p) := omega
                    break
                ancestor := ancestor.parent

            // Subsumption: skip if m' is covered by an existing node
            if not subsumed(m', existing_nodes):
                child := TreeNode(m')
                child.parent := node
                worklist.push(child)

    return tree
```

### 3.2. Deadlock Detection

```
function check_deadlock(net: PetriNet, initial: Marking, max_states: usize):
    visited := Set
    queue := Queue
    queue.push(initial)
    visited.insert(initial)

    while m := queue.pop():
        enabled := [t for t in net.transitions if net.is_enabled(t, m)]
        if enabled is empty:
            return DeadlockFound(m)

        for t in enabled:
            m' := fire(t, m)
            if m' not in visited and |visited| < max_states:
                visited.insert(m')
                queue.push(m')

    return NoDeadlock
```

### 3.3. Bron-Kerbosch Maximal Clique Enumeration

```
function extract_parallel_regions(net: PetriNet) -> Vec<ParallelRegion>:
    adj := build_independence_graph(net)
    cliques := []

    function bron_kerbosch(R, P, X):
        if P union X is empty:
            cliques.push(R)
            return
        pivot := vertex in P union X maximizing |P intersect N(pivot)|
        for v in P \ N(pivot):
            bron_kerbosch(R union {v}, P intersect N(v), X intersect N(v))
            P := P \ {v}
            X := X union {v}

    // Run per connected component for efficiency
    for component in connected_components(adj):
        bron_kerbosch({}, component, {})

    return cliques as ParallelRegions
```

## 4. Complexity Analysis

| Operation | Time | Space |
|-----------|------|-------|
| `construct_petri_net` | O(|P| + |T|) | O(|P| + |T|) |
| `is_enabled` | O(|pre(t)|) | O(1) |
| `fire` | O(|pre(t)| + |post(t)|) | O(|P|) |
| `check_deadlock` (BFS) | O(R * |T|) | O(R) |
| `check_coverability` (Karp-Miller) | O(2^{2^{O(|P|)}}) worst case | O(tree size) |
| `check_boundedness` | O(coverability tree size) | O(tree size) |
| `check_independence` | O(|arcs(t1)| + |arcs(t2)|) | O(max arcs) |
| `extract_parallel_regions` | O(3^{|T|/3}) worst case | O(|T|^2) |

Where: R = reachable state count, P = places, T = transitions.

The Karp-Miller tree can be exponentially large, but the `max_states` parameter
bounds the exploration in practice.

## 5. Unicode Diagrams

### 5.1. Petri Net Structure

```
    ┌─────────────────────────────────────────────────────┐
    │               Petri Net Example                     │
    │                                                     │
    │    (p0: chan_A)          (p1: chan_B)                │
    │       [2]                   [0]                     │
    │        │                     ^                      │
    │        │ consume 1           │ produce 1            │
    │        v                     │                      │
    │    ┌───────┐            ┌───────┐                   │
    │    │  t0   │───────────>│  t1   │                   │
    │    │ send  │            │ recv  │                   │
    │    └───────┘            └───────┘                   │
    │        │                     ^                      │
    │        │ produce 1           │ consume 1            │
    │        v                     │                      │
    │    (p2: buffer)          (p3: ack)                  │
    │       [0]                   [1]                     │
    │                                                     │
    └─────────────────────────────────────────────────────┘

    Initial marking: [2, 0, 0, 1]
    t0 enabled: p0 >= 1 and p3 >= 1 -> yes (2 >= 1 and 1 >= 1)
    After firing t0: [1, 0, 1, 0]
```

### 5.2. Karp-Miller Tree

```
    [2, 0, 0, 1]
         │
         │ fire t0
         v
    [1, 0, 1, 0]
         │
         │ fire t1
         v
    [1, 1, 0, 1]    <-- covers ancestor? No strict cover.
         │
         │ fire t0
         v
    [0, 1, 1, 0]
         │
         │ fire t1
         v
    [0, 2, 0, 1]    <-- p1 grew: 0 -> 1 -> 2. Not strictly covering.
         │
         └── no transitions enabled (deadlock if no more rules apply)
```

### 5.3. Independence Graph for Parallel Regions

```
    Transitions: t0, t1, t2, t3

    Independence graph:
      t0 ─── t2     (independent: no shared places)
      t1 ─── t3     (independent: no shared places)
      t0 ... t1     (dependent: share place p0)

    Maximal cliques:
      {t0, t2}  -> ParallelRegion(max_parallelism = 2)
      {t1, t3}  -> ParallelRegion(max_parallelism = 2)
```

## 6. PraTTaIL Integration

### 6.1. Pipeline Bridge Functions

- `construct_petri_net(categories)` -- Builds a Petri net from grammar categories
  with parallel composition.
- `PetriNet::check_deadlock(max_states)` -- BFS deadlock search.
- `PetriNet::check_coverability(target)` -- Karp-Miller coverability.
- `PetriNet::check_boundedness()` -- Boundedness via coverability tree.
- `PetriNet::extract_parallel_regions()` -- Bron-Kerbosch maximal cliques.
- `PetriNet::check_independence(t1, t2)` -- Pairwise independence test.
- `PetriNet::independence_relation()` -- All independent pairs.

### 6.2. Lint Emission

- **N01** (`deadlock-risk`): Emitted when deadlock detection finds a stuck
  marking. Severity: Warning. Diagnostic includes the deadlock marking and
  the last fired transition sequence.
- **N02** (`unbounded-channel`): Emitted when the Karp-Miller tree reveals an
  unbounded place. Severity: Warning. Diagnostic names the unbounded place(s).

### 6.3. Repair Integration

- Deadlock repair: suggest adding a "watchdog" transition that fires when all
  others are disabled.
- Unbounded channel repair: suggest adding capacity bounds to places.

## 7. Rust Implementation Notes

| Type | Role |
|------|------|
| `Place` | Place with id, name, optional capacity bound |
| `PetriTransition` | Transition with input/output arc vectors `(place_id, weight)` |
| `Marking` | Token vector indexed by place id |
| `PetriNet` | Full net: places, transitions, initial_marking |
| `ParallelRegion` | Maximal clique: transition indices + max_parallelism |
| `ParallelismReport` | Summary: all regions, max parallelism, independent pairs |

The Bron-Kerbosch implementation uses an **explicit stack** (not recursion) to
avoid stack overflow on large independence graphs. Connected components are
computed first via BFS so that isolated nodes (no independent partners) are
skipped.

## 8. Worked Example

**Rholang-inspired grammar:**
```
for (x <- chan_a) | (chan_b!(42))
```

**Petri net model:**
```
Places:  p0 = chan_a (capacity: 1), p1 = chan_b (unbounded)
Transitions:
  t0 = "send_b": outputs = [(p1, 1)]     // chan_b!(42)
  t1 = "recv_a": inputs = [(p0, 1)]      // for (x <- chan_a)
Initial marking: [1, 0]  // one message on chan_a
```

**Deadlock analysis:**
```
Initial:  [1, 0]
  t1 enabled (p0 >= 1): fire -> [0, 0]
  t0 enabled (no inputs): fire -> [0, 1]
  From [0, 0]: only t0 enabled -> [0, 1]
  From [0, 1]: only t0 enabled -> [0, 2]
    ...p1 unbounded!
  No deadlock found (t0 always enabled).
```

**Boundedness:** p1 is unbounded (N02 emitted).

**Independence:** t0 and t1 are independent (disjoint place sets), so they
form a parallel region with max_parallelism = 2.

## 9. References

1. Karp, R.M. & Miller, R.E. (1969).
   "Parallel Program Schemata."
   *Journal of Computer and System Sciences*, 3(2), pp. 147--195.

2. Mayr, E.W. (1981).
   "An Algorithm for the General Petri Net Reachability Problem."
   *Proc. 13th Annual ACM Symposium on Theory of Computing (STOC)*, pp. 238--246.

3. Esparza, J. & Nielsen, M. (1994).
   "Decidability Issues for Petri Nets -- a Survey."
   *Bulletin of the EATCS*, 52, pp. 245--262.

4. Petri, C.A. (1962).
   *Kommunikation mit Automaten.*
   PhD thesis, University of Bonn.

5. Bron, C. & Kerbosch, J. (1973).
   "Algorithm 457: Finding All Cliques of an Undirected Graph."
   *Communications of the ACM*, 16(9), pp. 575--577.
