# BuchiWpdsProduct.v -- Product Construction and SCC-Based Emptiness

**File:** `formal/rocq/mathematical_analyses/theories/BuchiWpdsProduct.v`
**Lines:** 635
**Admitted:** 0
**Dependencies:** Builds on the WPDS model from `WpdsCorrectness.v`
(conceptually; technically re-parameterized as standalone).


## Intuition

LTL model checking asks: "does a system satisfy a temporal property
like 'every request is eventually followed by a response'?" The
standard automata-theoretic approach converts this to an emptiness
problem: negate the property, convert it to a Buchi automaton, take the
product with the system, and check whether the product has an accepting
run. If it does, the property is violated; if not, the property holds.

PraTTaIL uses this approach to check liveness properties of grammar
rule interactions. The WPDS models the pushdown parsing process; the
Buchi automaton encodes the negated property. The product captures
exactly those WPDS runs that violate the property. Emptiness of the
product means the property is satisfied.

This proof file establishes that the product construction is **sound**
(every product accepting run projects to a valid WPDS run and a Buchi
accepting run) and **complete** (every synchronized pair of WPDS run +
Buchi accepting run lifts to a product accepting run). It also proves
that SCC-based emptiness is a correct decision procedure.


## What It Proves

### Graph SCC Infrastructure

Foundational definitions for strongly connected components:

| Definition/Theorem | Statement |
|-------------------|-----------|
| `graph_reach` | Reflexive-transitive closure of edge |
| `graph_reach_trans` | Reachability is transitive |
| `in_same_scc` | Mutual reachability: i reaches j and j reaches i |
| `in_same_scc_refl` | SCC membership is reflexive |
| `in_same_scc_sym` | SCC membership is symmetric |
| `in_same_scc_trans` | SCC membership is transitive |
| `scc_has_cycle` | An SCC has a cycle if it has >1 member or a self-loop |

The three SCC membership lemmas establish that `in_same_scc` is an
**equivalence relation**, which justifies treating SCCs as equivalence
classes.

### Buchi Automaton Model

| Definition | Meaning |
|-----------|---------|
| `buchi_run` | Finite run segment: sequence of transitions |
| `has_accepting_cycle` | Initial state reaches an accepting state that loops |
| `buchi_empty` | No accepting cycle exists |
| `buchi_edge` | Transition relation with label existentially quantified |
| `buchi_reachable` | Reachable from an initial state |
| `has_accepting_scc` | Reachable accepting state on a non-trivial cycle |

**SCC equivalence theorem:**

```
Theorem buchi_emptiness_scc_equiv :
  has_accepting_cycle <-> has_accepting_scc.
```

A Buchi automaton has an accepting run if and only if there exists a
reachable SCC containing an accepting state with at least one edge.

### WPDS Model

| Definition | Meaning |
|-----------|---------|
| `wpds_config` | Stack configuration (list of stack symbols) |
| `wpds_step` | One-step transition relation |
| `wpds_run` | Sequence of WPDS configurations |

### Product Construction

| Definition | Meaning |
|-----------|---------|
| `product_config` | Pair: (Buchi state, WPDS stack) |
| `product_step` | WPDS steps and Buchi reads the result |
| `product_run` | Sequence of product configurations |
| `product_initial` | Buchi component is an initial state |
| `product_accepting` | Buchi component is an accepting state |
| `product_has_accepting_cycle` | Product has an accepting run |

### Main Theorems

**Soundness:**

```
Theorem product_soundness :
  product_has_accepting_cycle ->
  (exists stk_i stk_f stks1 stks2,
    wpds_run wpds_step stk_i stks1 stk_f /\
    wpds_run wpds_step stk_f stks2 stk_f /\
    stks2 <> []) /\
  has_accepting_cycle buchi_trans buchi_initial buchi_accepting.
```

A product accepting cycle implies both a valid WPDS run (with a cycle)
and a Buchi accepting cycle.

**Completeness:**

```
Theorem product_completeness :
  ... ->
  forall qi qf stk_i stk_f stks1 stks2,
    buchi_initial qi -> buchi_accepting qf ->
    wpds_run stk_i stks1 stk_f ->
    buchi_run qi stks1 qf ->
    wpds_run stk_f stks2 stk_f ->
    buchi_run qf stks2 qf ->
    stks2 <> [] ->
    product_has_accepting_cycle.
```

A synchronized WPDS run + Buchi accepting cycle lifts to a product
accepting cycle.

**SCC emptiness soundness:**

```
Theorem scc_emptiness_sound :
  forall pc_acc,
    product_accepting pc_acc ->
    (exists pc_init, product_initial pc_init /\
                     product_reach pc_init pc_acc) ->
    (exists pc_mid, product_edge pc_acc pc_mid /\
                    product_reach pc_mid pc_acc) ->
    product_has_accepting_cycle.
```

If a reachable accepting product configuration lies on a non-trivial
cycle, the product has an accepting cycle.


## Why It Matters

```
  ┌───────────────────────────────────────────────────────────┐
  │  Pipeline: LTL property checking for grammar rules        │
  │  "Does every recursive call eventually return?"           │
  ├───────────────────────────────────────────────────────────┤
  │                                                           │
  │  WPDS (parsing model)       Buchi (negated property)      │
  │        │                          │                       │
  │        └────────── x ─────────────┘                       │
  │                    │                                      │
  │             Product WPDS                                  │  <-- THIS
  │                    │                                      │
  │             SCC emptiness check                           │  <-- THIS
  │                    │                                      │
  │             accepts / rejects                             │
  │                                                           │
  └───────────────────────────────────────────────────────────┘
```

The product construction and SCC emptiness check are the decision
procedure for liveness properties of the grammar's pushdown behavior.
The Rust implementation in `buchi.rs` uses Tarjan's SCC algorithm to
find strongly connected components and checks each for accepting states.
This proof file guarantees that the algorithm is correct.


## Proof Strategy

### Product State Space Diagram

The product runs the WPDS and Buchi automaton in lockstep. At each step,
the WPDS takes a step (changing the stack), and the Buchi reads the
resulting configuration as its input label:

```
  WPDS stack:    stk0 ──step──> stk1 ──step──> stk2 ──step──> stk3
                   │              │               │              │
                   v              v               v              v
  Buchi:         q0 ──stk1───> q1 ──stk2────> q2 ──stk3────> q3
                   │              │               │              │
                   v              v               v              v
  Product:    (q0,stk0) ────> (q1,stk1) ────> (q2,stk2) ────> (q3,stk3)
```

A product step `(q1, stk1) -> (q2, stk2)` requires both:
1. `wpds_step stk1 stk2` (WPDS can make this stack transition)
2. `buchi_trans q1 stk2 q2` (Buchi can read stk2 and transition)

### Soundness: Projection

The soundness proof projects a product run to its two components:

```
Lemma product_run_proj_wpds : forall pc1 pcs pc3,
  product_run pc1 pcs pc3 ->
  wpds_run (snd pc1) (map snd pcs) (snd pc3).

Lemma product_run_proj_buchi : forall pc1 pcs pc3,
  product_run pc1 pcs pc3 ->
  buchi_run (fst pc1) (map snd pcs) (fst pc3).
```

Both projections are proven by induction on the product run.
Destructing the product step gives both `wpds_step` and `buchi_trans`.
The non-emptiness of the cycle (`stks2 <> []`) is preserved because
`map snd` preserves list length.

### Completeness: Run Combination

The completeness proof *combines* a WPDS run and a Buchi run into a
product run. The key lemma is:

```
Lemma combine_runs : forall q1 stk1 stks q2 stk2,
  wpds_run stk1 stks stk2 ->
  buchi_run q1 stks q2 ->
  exists pcs, product_run (q1, stk1) pcs (q2, stk2) /\
              map snd pcs = stks.
```

The proof proceeds by induction on the WPDS run, inversing the Buchi
run at each step to extract the matching transition. The `map snd pcs =
stks` invariant ensures the combined run uses the same configuration
sequence.

### SCC Equivalence: Cycle Detection

The Buchi SCC equivalence theorem (`buchi_emptiness_scc_equiv`) shows
that the SCC-based emptiness check is sound and complete:

**Forward (accepting cycle implies accepting SCC):**

1. Convert the Buchi run to graph reachability (`buchi_run_to_graph_reach`)
2. The reaching phase gives `graph_reach qi qf`
3. The cycling phase gives an edge from qf plus a path back

**Backward (accepting SCC implies accepting cycle):**

1. Convert graph reachability back to Buchi runs (`graph_reach_to_buchi_run`)
2. The edge from qf gives the first transition of the cycle
3. The path back completes the cycle
4. The cycle is non-empty (at least one transition)

The conversion between `buchi_run` and `graph_reach` uses:

```
Lemma buchi_run_to_graph_reach : forall q1 w q2,
  buchi_run q1 w q2 -> graph_reach buchi_edge q1 q2.

Lemma graph_reach_to_buchi_run : forall q1 q2,
  graph_reach buchi_edge q1 q2 -> exists w, buchi_run q1 w q2.
```

The first direction is straightforward (every transition is an edge).
The second direction converts each `buchi_edge` (existential label)
back to a concrete transition label.


### SCC as Equivalence Relation

The proof establishes that `in_same_scc` is an equivalence relation,
which justifies the partition of nodes into SCCs:

```
  ┌─────────────────────────────────────────────────┐
  │  in_same_scc is:                                │
  │                                                 │
  │    Reflexive:   graph_reach_refl gives both      │
  │                 directions trivially             │
  │                                                 │
  │    Symmetric:   swap the two components of the   │
  │                 conjunction                      │
  │                                                 │
  │    Transitive:  compose reachability paths via    │
  │                 graph_reach_trans                 │
  │                                                 │
  │  Therefore: SCCs partition the node set into     │
  │  equivalence classes.                            │
  └─────────────────────────────────────────────────┘
```

A non-trivial SCC (one that has a cycle) is detected by checking either:
- More than one member (multi-node SCC), or
- A self-loop (single-node SCC with an edge to itself)

This matches the Tarjan SCC implementation in `buchi.rs:462-575`, which
identifies SCCs and checks each for accepting states.


## Rust Code Traceability

| Rocq Definition | Rust Counterpart | File |
|----------------|-----------------|------|
| `wpds_config` | `StackSymbol` + `WpdsRule` | `wpds.rs:62-133` |
| `wpds_step` | poststar saturation | `wpds.rs` |
| `buchi_state` (nat) | `BuchiState` | `buchi.rs:58-69` |
| `buchi_trans` | `BuchiTransition` | `buchi.rs:112-131` |
| `buchi_run` | Run segment tracking | `buchi.rs` |
| `has_accepting_cycle` | Buchi acceptance condition | `buchi.rs` |
| `product_config` | Product construction in pipeline | `pipeline.rs` |
| `product_step` | Synchronized WPDS + Buchi step | `buchi.rs:277-385` |
| `buchi_intersect` | `buchi_intersect()` | `buchi.rs:277-385` |
| `check_emptiness` | `check_emptiness()` | `buchi.rs:402-578` |
| `scc_has_accepting` | Tarjan SCC + accepting check | `buchi.rs:462-575` |
| `graph_reach` | Reachability in transition graph | `buchi.rs` |
| `in_same_scc` | SCC membership | `buchi.rs` (Tarjan) |


## Theoretical References

- Reps, T., Lal, A. & Kidd, N. (2007). "Program analysis using
  weighted pushdown systems." FSTTCS 2003. WPDS saturation algorithms.
- Vardi, M. & Wolper, P. (1994). "Reasoning about infinite
  computations." Information and Computation 115(1). Automata-theoretic
  model checking framework.
- Schwoon, S. (2002). "Model-Checking Pushdown Systems." PhD thesis.
  Product of pushdown systems with Buchi automata.
- Esparza, J., Hansel, D., Rossmanith, P. & Schwoon, S. (2000).
  "Efficient algorithms for model checking pushdown systems." CAV 2000.
  Decidability of LTL model checking for PDS.
