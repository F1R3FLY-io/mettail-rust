# Concurrency Analysis

**Source files:** `petri.rs`, `nominal.rs`, `alternating.rs`
**Pipeline phase:** 4 (no dependencies)
**Feature gates:** `petri`, `nominal`, `alternating`
**Convenience group:** `process-algebra` (all three plus `omega`)

## Rationale

PraTTaIL generates parsers for the Rho calculus (MeTTaIL), which is an
inherently concurrent language.  `PNew` introduces fresh names, `PPar`
composes processes in parallel, and communication occurs via name-passing
on channels.  Three process-algebraic models address different aspects:

- **Petri nets** model resource consumption and production during
  concurrent parsing, detecting deadlocks and unbounded resource growth.
- **Nominal automata** track name binding and scope, ensuring that variable
  references respect the scoping discipline of `PNew` and `PInput`.
- **Alternating bisimulation** verifies that grammar categories with
  similar structure accept equivalent languages, even in the presence of
  universal (all-branches-must-accept) constraints.

---

## 1. Petri Nets and VASS (`petri.rs`)

### 1.1 Intuition

A Petri net models a concurrent system as a bipartite graph of places
(holding tokens) and transitions (consuming/producing tokens).  The current
state is a *marking* -- the distribution of tokens across places.  A
transition is *enabled* when all its input places have sufficient tokens;
*firing* removes input tokens and adds output tokens.

For PraTTaIL, places represent resources (tokens in the input stream,
parser stack slots, available channel buffers) and transitions represent
parsing actions (shift, reduce, send, receive).

### 1.2 Formal Definition

A Petri net is `N = (P, T, Pre, Post, m0)` where:

- `P` -- finite set of places
- `T` -- finite set of transitions
- `Pre: T x P -> N` -- input weight (tokens consumed from place `p` by
  transition `t`)
- `Post: T x P -> N` -- output weight (tokens produced in place `p` by
  transition `t`)
- `m0: P -> N` -- initial marking

A transition `t` is **enabled** at marking `m` iff `forall p: m(p) >= Pre(t, p)`.

Firing `t` produces marking `m'` where:

```
  m'(p) = m(p) - Pre(t, p) + Post(t, p)    for all p in P
```

### 1.3 Coverability via Karp-Miller Tree

The coverability problem asks: "from `m0`, can we reach a marking `m`
where `m >= m_target`?"  The Karp-Miller tree explores the reachability
graph, using `omega` (infinity) to represent unbounded growth:

```
function karp_miller(net, m0) -> KarpMillerTree:
    root := node(m0)
    worklist := [root]
    while worklist is non-empty:
        node := worklist.pop()
        if node.marking is a proper ancestor's marking:
            continue  // already explored
        for each enabled transition t at node.marking:
            m' := fire(t, node.marking)
            // Acceleration: if m' > some ancestor marking m_anc,
            // set m'(p) := omega for each p where m'(p) > m_anc(p)
            for each ancestor a of node:
                if m' >= a.marking and m' != a.marking:
                    for p in P:
                        if m'(p) > a.marking(p):
                            m'(p) := omega
            child := node.add_child(m', t)
            worklist.push(child)
    return tree
```

A place is **bounded** if its value never reaches `omega` in the
Karp-Miller tree.  The net is **bounded** iff all places are bounded.

### 1.4 Deadlock Detection

A marking `m` is a **deadlock** if no transition is enabled:

```
function check_deadlock(net, m0) -> DeadlockResult:
    tree := karp_miller(net, m0)
    for each leaf node n in tree:
        if no transition is enabled at n.marking:
            return Deadlock { marking: n.marking, trace: path_to(n) }
    return DeadlockFree
```

### 1.5 Boundedness Check

```
function check_boundedness(net, m0) -> BoundednessResult:
    tree := karp_miller(net, m0)
    unbounded_places := { p | exists node n in tree: n.marking(p) == omega }
    if unbounded_places is empty:
        return Bounded { bounds: max_marking_per_place(tree) }
    else:
        return Unbounded { places: unbounded_places }
```

### 1.6 Diagram: Petri Net Firing

```
  Before firing t1:               After firing t1:

  Place p1: @@  (2 tokens)        Place p1: @   (1 token)
  Place p2: @   (1 token)         Place p2: @@  (2 tokens)
  Place p3:     (0 tokens)        Place p3: @   (1 token)

      p1 ──(2)──▶ [t1] ──(1)──▶ p2
                    │
                   (1)
                    │
                    ▼
                   p3

  Pre(t1, p1) = 2, Pre(t1, p2) = 0, Pre(t1, p3) = 0
  Post(t1, p1) = 1, Post(t1, p2) = 2, Post(t1, p3) = 1
  Effect: p1: 2-2+1=1, p2: 1-0+2=3 (shown as 2 for fit), p3: 0-0+1=1
```

### 1.7 Diagram: Karp-Miller Tree with Omega

```
  Initial marking: m0 = (1, 0)
  Transitions: t1: p1 -> p1 + p2  (one token from p1, one to p1 and one to p2)
               t2: p2 -> (nothing) (consume from p2)

  Tree:
                    (1, 0)
                      │  fire t1
                      ▼
                    (1, 1)           m' > m0 at p2, so:
                      │  fire t1
                      ▼
                    (1, omega)       p2 set to omega (unbounded)
                    ╱        ╲
              fire t1      fire t2
                ╱              ╲
          (1, omega)        (1, omega)
           (same)           (same -- omega - 1 = omega)

  Result: p2 is UNBOUNDED; p1 is bounded at 1.
```

### 1.8 Pipeline Bridge

```rust
pub fn analyze_from_bundle(
    all_syntax: &[(String, String, Vec<SyntaxItemSpec>)],
    categories: &[WpdsCategoryInfo],
) -> PetriAnalysis
```

Constructs a Petri net from the grammar:
- Each category becomes a place
- Each rule becomes a transition consuming from its category's place and
  producing into referenced categories' places
- Primary categories start with one token

Returns `PetriAnalysis` with deadlock detection and boundedness results.

---

## 2. Nominal Automata (`nominal.rs`)

### 2.1 Intuition

Classical automata have a finite alphabet.  Name-passing calculi like the
Rho calculus generate fresh names dynamically (`PNew`), creating an
effectively infinite alphabet.  Nominal automata handle this by exploiting
the symmetry of names: two configurations that differ only in the choice of
names are equivalent.

The key insight from Bojańczyk, Klin & Lasota (2014) is that while the
raw state space is infinite, it has only finitely many *orbits* under the
name permutation group.  An orbit-finite automaton can be represented and
analysed finitely.

### 2.2 Key Concepts

**Atom** `a in A` -- a name from an infinite set (e.g., Rho calculus
channel names).

**Support** `supp(x)` -- the smallest set of atoms such that any
permutation fixing `supp(x)` also fixes `x`.  A finite-support element is
determined (up to permutation) by its support.

**Orbit** `Orb(x)` -- the set `{ pi(x) | pi is a permutation }`.  An
orbit-finite set has finitely many orbits.

**Equivariant function** `f` -- a function satisfying
`f(pi(x)) = pi(f(x))` for all permutations `pi`.  Equivariant transition
functions preserve the symmetry structure.

### 2.3 Formal Definition

A nominal automaton is `A = (Q, Sigma, delta, Q0, F)` where:

- `Q` -- orbit-finite set of states (with finite support)
- `Sigma` -- orbit-finite input alphabet
- `delta: Q x Sigma -> Q` -- equivariant transition function
- `Q0 subset Q` -- initial states (equivariant subset)
- `F subset Q` -- accepting states (equivariant subset)

### 2.4 Scope Checking

For PraTTaIL, the primary application is scope checking.  Each `Binder`
position introduces a fresh atom.  The nominal automaton tracks which
atoms are in scope at each parse state:

```
function check_scope(syntax_items, binder_positions) -> ScopeResult:
    in_scope := {}  // set of atoms currently in scope
    for each item in syntax_items:
        match item:
            Binder(name, category) =>
                fresh := new_atom(name)
                in_scope.add(fresh)
            NonTerminal(category, param_name) =>
                // Check that referenced names are in scope
                for each free_name in free_names(param_name):
                    if free_name not in in_scope:
                        return ScopeViolation { name: free_name, position }
    return AllInScope
```

### 2.5 Orbit Structure Diagram

```
  Atoms: a, b, c, d, ...

  State orbit examples for 2-register nominal automaton:
  ┌────────────────────────────────────────────┐
  │  Orbit 0: (emptyset)  -- no names in scope │
  │  Representative: q(emptyset)                │
  ├────────────────────────────────────────────┤
  │  Orbit 1: ({a})  -- one name in scope      │
  │  Representatives: q({a}), q({b}), q({c})   │
  │  (all equivalent under renaming)            │
  ├────────────────────────────────────────────┤
  │  Orbit 2: ({a, b})  -- two names in scope  │
  │  Representatives: q({a,b}), q({a,c}), ...  │
  └────────────────────────────────────────────┘

  Three orbits, but infinitely many concrete states.
  The automaton operates on orbits, not individual states.
```

### 2.6 Pipeline Bridge

```rust
pub fn analyze_from_bundle(
    all_syntax: &[(String, String, Vec<SyntaxItemSpec>)],
) -> NominalAnalysis
```

Scans all syntax items for `Binder` and `BinderCollection` positions.
Builds the scope map and checks for violations.  Returns `NominalAnalysis`
with scope violation list and binder statistics.

---

## 3. Alternating Bisimulation (`alternating.rs`)

### 3.1 Intuition

Bisimulation is the process-algebraic notion of behavioural equivalence:
two systems are bisimilar if they can match each other's transitions step
by step.  For alternating automata, bisimulation must account for both
existential and universal branching.

In PraTTaIL, bisimulation checking verifies that two grammar categories
accepting similar syntax actually accept the same language.  This is useful
for detecting redundant categories and for validating grammar refactoring.

### 3.2 Bisimulation Game

The bisimulation game is played between an Attacker (trying to distinguish
the two automata) and a Defender (trying to show they are equivalent):

```
  Position: (state_in_A, state_in_B)

  Round:
    1. Attacker picks a transition from A (or B) on some label l
    2. Defender must match: find a transition on the same label l in B (or A)
    3. If Defender cannot match → Attacker wins (not bisimilar)
    4. The game continues with the successor position

  Infinite play: Defender wins (bisimulation holds)
```

### 3.3 Attractor Computation

The Attacker's winning set is computed by backward propagation:

```
function compute_attacker_wins(A, B) -> Set<Position>:
    wins := {}
    // Phase 1: immediate wins (unmatched labels)
    for (pa, pb) in Q_A x Q_B:
        if labels(A, pa) != labels(B, pb):
            wins.add((pa, pb))
    // Phase 2: backward propagation
    changed := true
    while changed:
        changed := false
        for (pa, pb) not in wins:
            // Attacker wins if there exists a label l such that
            // for ALL matching transitions by Defender,
            // SOME successor pair is already a win for Attacker
            for each (label, succs_a) in transitions(A, pa):
                for each (label, succs_b) in transitions(B, pb) matching label:
                    if any((sa, sb) in succs_a x succs_b where (sa,sb) in wins):
                        wins.add((pa, pb))
                        changed := true
    return wins
```

Bisimulation holds iff `(init_A, init_B) not in wins`.

### 3.4 PraTTaIL Application

Each grammar category becomes an alternating automaton:
- **Root state** (existential): the parser tries alternative rules
- **Rule states** (universal): all syntax items in a rule must match
- **Item states** (existential): each item is a leaf

Pairwise bisimulation checks identify categories that are structurally
different, surfaced as N05 lint diagnostics.

### 3.5 Complexity

| Operation              | Time complexity                |
|------------------------|-------------------------------|
| Emptiness (fixpoint)   | O(|Q| * |delta|)             |
| Bisimulation game      | O(|Q_A| * |Q_B| * |Sigma|^2) |
| Attractor computation  | O(|Q_A|^2 * |Q_B|^2 * |delta|) per iteration |

---

## 4. Interaction Between Concurrency Analyses

The three concurrency analyses provide complementary views:

```
  ┌──────────────────────────────────────────────────────────┐
  │                     Grammar Specification                │
  │                                                          │
  │   ┌─────────┐    ┌───────────┐    ┌──────────────────┐  │
  │   │ Petri   │    │ Nominal   │    │   Alternating    │  │
  │   │ Net     │    │ Automaton │    │   Bisimulation   │  │
  │   │         │    │           │    │                  │  │
  │   │Resources│    │  Names    │    │   Structure      │  │
  │   │ & flow  │    │  & scope  │    │   equivalence    │  │
  │   └────┬────┘    └─────┬─────┘    └────────┬─────────┘  │
  │        │               │                   │             │
  │        ▼               ▼                   ▼             │
  │   N01: deadlock   N03: scope          N05: bisim         │
  │   N02: safe       N04: in-scope       summary            │
  └──────────────────────────────────────────────────────────┘
```

- **Petri** answers: "Can the parser get stuck (deadlock)? Can buffers grow
  without bound?"
- **Nominal** answers: "Are all variable references in scope? Does
  alpha-equivalence hold?"
- **Alternating** answers: "Do structurally similar categories accept the
  same language?"

---

## 5. References

- C.A. Petri (1962). *Kommunikation mit Automaten*. PhD thesis, University
  of Bonn.
- R.M. Karp & R.E. Miller (1969). "Parallel program schemata." *JCSS*,
  3(2), pp. 147--195.
- E.W. Mayr (1981). "An algorithm for the general Petri net reachability
  problem." *STOC 1981*, pp. 238--246.
- J. Esparza & M. Nielsen (1994). "Decidability issues for Petri nets."
  *BRICS Report Series*, RS-94-8.
- M. Bojańczyk, B. Klin & S. Lasota (2014). "Automata theory in nominal
  sets." *Logical Methods in Computer Science*, 10(3).
- A.M. Pitts (2013). *Nominal Sets: Names and Symmetry in Computer
  Science*. Cambridge University Press.
- A.K. Chandra, D.C. Kozen & L.J. Stockmeyer (1981). "Alternation."
  *JACM*, 28(1), pp. 114--133.
- M. Jurdzinski (2000). "Small progress measures for solving parity
  games." *STACS 2000*, LNCS 1770.
