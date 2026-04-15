# Heyting Algebra Extensions for Predicated Types

**Companion to:** [Why Automata Instead of Solvers](why-automata-instead-of-solvers.md)
**See also:** [Symbolic Automata Research Analysis](symbolic-automata-research-analysis.md)
**Status:** RESEARCH DIRECTION -- this document describes an **unimplemented**
proposal.  No code exists for Heyting algebra backends.

---

This document provides the expanded formal treatment of Heyting algebra
extensions for MeTTaIL's predicated types framework.  The main document's
§11 ([Why Automata Instead of Solvers](why-automata-instead-of-solvers.md))
introduces the concept; this document develops the theory, provides concrete
MeTTaIL use cases, and sketches a Rust implementation architecture.

---

> **Status:** This entire section describes an **unimplemented research
> direction**.  No code exists for Heyting algebra backends.

The main document's §11 introduces Heyting algebras as a potential
extension for predicated types over non-Boolean domains (graph reachability,
topological closure, constructive properties).  This section provides the
deeper formal treatment.

## 1. Formal Foundations

To define a Heyting algebra precisely, we build up from simpler structures.
Each layer adds a new capability that the predicated types framework uses.

### 1.1 Partial Orders

A **partial order** `(H, ≤)` is a set `H` with a binary relation `≤` that
satisfies three properties:

- **Reflexive:** `a ≤ a` — every element is related to itself
- **Antisymmetric:** `a ≤ b ∧ b ≤ a ⟹ a = b` — if two elements are
  mutually below each other, they are the same element
- **Transitive:** `a ≤ b ∧ b ≤ c ⟹ a ≤ c` — the ordering chains

The word "partial" means that not every pair of elements needs to be
comparable: it is valid for two elements `a` and `b` to be **incomparable**
(`a ≰ b` and `b ≰ a`).  This distinguishes a partial order from a total
order (where every pair is comparable, like integers under `≤`).

**Intuition.** A partial order models "strength of information" or
"specificity of predicates."  When `a ≤ b`, element `a` is weaker, less
specific, or less informative than `b`.  Two elements can be incomparable
when they carry orthogonal information — neither implies the other.

**MeTTaIL application.** Guard predicates on a channel form a partial order
under **implication**: `φ ≤ ψ` means "every value satisfying `φ` also
satisfies `ψ`" — i.e., `φ` is more specific than `ψ`.  Two guards like
`x ≥ 10` and `name = "foo"` are incomparable (neither implies the other).
The subsumption analysis in the main document §2.3 is precisely this partial
order: `φᵢ` subsumes `φⱼ` iff `φⱼ ≤ φᵢ` in the predicate ordering.

### 1.2 Lattices

A **lattice** is a partial order where every pair of elements has:

- A **meet** `a ∧ b` (greatest lower bound): the strongest element that is
  below both `a` and `b`
- A **join** `a ∨ b` (least upper bound): the weakest element that is above
  both `a` and `b`

**Intuition.** Given two predicates, the meet is their conjunction ("both
must hold") and the join is their disjunction ("at least one must hold").
The meet is "strongest common consequence" — the most you can conclude from
both predicates together.  The join is "weakest common generalization" — the
least you need to say to cover both predicates.

**Example.** For integer interval guards: `meet([0, 50), [30, 100)) = [30, 50)`
(the overlap region — values satisfying both), and
`join([0, 50), [30, 100)) = [0, 100)` (the union — values satisfying either).

**MeTTaIL application.** The `BooleanAlgebra` trait's `and(φ, ψ)` and
`or(φ, ψ)` are exactly the meet and join operations.  When the compiler
computes `SAT(φᵢ ∧ φⱼ)` for overlap detection (main document §2.3), it is
computing the meet and checking whether it is above `⊥`.

### 1.3 Bounded Lattices

A **bounded lattice** adds two distinguished elements:

- A **bottom** `⊥` (below everything: `⊥ ≤ a` for all `a ∈ H`)
- A **top** `⊤` (above everything: `a ≤ ⊤` for all `a ∈ H`)

**Intuition.** `⊥` is the **contradiction** — a predicate so strong that no
value satisfies it (the empty set).  `⊤` is the **tautology** — a predicate
so weak that every value satisfies it (the entire domain).  Every lattice of
predicates has these: the impossible guard and the accept-everything guard.

**MeTTaIL application.** `BooleanAlgebra::false_pred()` returns `⊥` and
`BooleanAlgebra::true_pred()` returns `⊤`.  A guard that is `⊥` is dead
code (the compiler eliminates it).  A guard that is `⊤` is unconditional
(every value passes — equivalent to an unguarded receive).

### 1.4 Distributive Lattices

A **distributive lattice** is a lattice where meet distributes over join:

    a ∧ (b ∨ c) = (a ∧ b) ∨ (a ∧ c)

and equivalently, join distributes over meet:

    a ∨ (b ∧ c) = (a ∨ b) ∧ (a ∨ c)

**Intuition.** Distributivity means: "A and (B or C)" is the same as
"(A and B) or (A and C)."  This is the familiar law from Boolean logic,
and it holds in most predicate algebras encountered in practice.  However,
not all lattices are distributive — the **diamond lattice** `M₃` (five
elements with three incomparable middle elements) and the **pentagon
lattice** `N₅` are the two minimal counterexamples.  Birkhoff's theorem
states that a lattice is distributive if and only if it contains neither
`M₃` nor `N₅` as a sublattice.

**MeTTaIL application.** Distributivity ensures that minterm computation
is well-defined: minterms partition the domain into regions because `∧` and
`∨` interact predictably.  If the lattice were non-distributive, the
minterm partition could have "holes" where the two operations disagree about
the structure of the domain.

### 1.5 Connection to WFST Semiring Lattices

MeTTaIL's Weighted Finite State Transducers (WFSTs) use **semirings** to
assign weights to transitions.  A semiring `(S, ⊕, ⊗, 0̄, 1̄)` has two
operations — `⊕` (combine paths) and `⊗` (extend a path) — with identity
elements `0̄` (no path) and `1̄` (empty path).  The most common semiring in
dispatch ranking is the **tropical semiring** (`⊕ = min`, `⊗ = +`), where
the cheapest path wins.

The connection to lattices: **every bounded lattice `(L, ⊥, ⊤, ∧, ∨)` is a
semiring** with `⊕ = ∨` (join) and `⊗ = ∧` (meet), `0̄ = ⊥`, `1̄ = ⊤`.
This is called the **lattice semiring**.  Conversely, many semirings used in
WFSTs have an underlying lattice structure — the natural ordering
`a ≤ b ⟺ a ⊕ b = b` gives a partial order that often forms a lattice.

| WFST semiring | `⊕` (combine) | `⊗` (extend) | Underlying lattice?             | MeTTaIL use                           |
|---------------|---------------|--------------|---------------------------------|---------------------------------------|
| Tropical      | `min`         | `+`          | Yes: `a ≤ b ⟺ a ≥ b` (reversed) | Dispatch ranking (cheapest path wins) |
| Log           | `⊕_log`       | `+`          | Yes (reversed)                  | Probabilistic selectivity (M7)        |
| Boolean       | `∨`           | `∧`          | Yes: the two-element lattice    | Guard satisfiability (SAT)            |
| Lattice       | `∨`           | `∧`          | By definition                   | Heyting/Boolean guard analysis        |

The Heyting algebra adds `→` (implication) to the lattice semiring — an
operation that semirings do not have.  This is the additional structure
needed for guard subsumption analysis: `φ → ψ` answers "does `φ` imply
`ψ`?" as a first-class predicate, which pure semiring operations cannot
express.  The WFST's tropical semiring can rank dispatch alternatives by
cost, but it cannot analyze guard implication — that requires the lattice
structure extended with `→`.

**Symbols used in the definitions below:**

| Symbol   | Name                  | Read as                    | Meaning                                                                                                                               |
|----------|-----------------------|----------------------------|---------------------------------------------------------------------------------------------------------------------------------------|
| `≤`      | Partial order         | "is below" or "implies"    | `a ≤ b` means `a` is at most `b` in the ordering                                                                                      |
| `∧`      | Meet (conjunction)    | "and"                      | Greatest lower bound of two elements                                                                                                  |
| `∨`      | Join (disjunction)    | "or"                       | Least upper bound of two elements                                                                                                     |
| `⊥`      | Bottom                | "false" or "contradiction" | The least element — below everything                                                                                                  |
| `⊤`      | Top                   | "true" or "tautology"      | The greatest element — above everything                                                                                               |
| `→`      | Heyting implication   | "implies" (constructively) | Largest `c` such that `a ∧ c ≤ b`                                                                                                     |
| `¬`      | Pseudo-complement     | "not" (Heyting)            | Defined as `¬a ≝ (a → ⊥)`                                                                                                             |
| `≝`      | Definitional equality | "is defined as"            | Introduces a definition                                                                                                               |
| `⟺`      | If and only if        | "iff"                      | Biconditional — both directions hold                                                                                                  |
| `∈`      | Element of            | "belongs to"               | `a ∈ H` means `a` is an element of set `H`                                                                                            |
| `H`      | Carrier set           | "the algebra"              | The set of all elements (predicates) in the Heyting algebra — every guard predicate that the algebra can express is an element of `H` |
| `⊆`      | Subset                | "is contained in"          | `A ⊆ B` means every element of `A` is also in `B`                                                                                     |
| `⊇`      | Superset              | "contains"                 | `A ⊇ B` means `A` contains every element of `B`                                                                                       |
| `∖`      | Set difference        | "minus"                    | `A ∖ B` is the set of elements in `A` but not in `B`                                                                                  |
| `cl(U)`  | Closure               | "the closure of U"         | The smallest closed set containing `U` — adds all boundary/limit points                                                               |
| `int(U)` | Interior              | "the interior of U"        | The largest open set contained in `U` — removes boundary points                                                                       |

**Definition (Heyting Algebra).** A **Heyting algebra** is a bounded
distributive lattice `(H, ⊥, ⊤, ∧, ∨)` equipped with a binary operation
`→ : H × H → H` (the **Heyting implication** or **relative
pseudo-complement**) satisfying the **adjunction** below.

An **adjunction** (also called a **Galois connection**) is a pair of
operations that are "undo partners" in an asymmetric sense: one operation
(here `∧`, meet/conjunction) has a counterpart (here `→`, implication) such
that asking "does `a ∧ c ≤ b`?" is equivalent to asking "does `c ≤ (a → b)`?"
The two questions always give the same answer, for any choice of `a`, `b`,
`c`.  This equivalence is what makes `→` the "best possible" implication
operation for the lattice — it is uniquely determined by `∧` and `≤`.

Formally:

    a ∧ c ≤ b   ⟺   c ≤ (a → b)

for all `a, b, c ∈ H`.  Read the left side as: "`c` combined with `a`
is below `b`" — i.e., assuming both `a` and `c`, we can conclude `b`.
Read the right side as: "`c` alone is below `a → b`" — i.e., `c` is
a weaker statement than "if `a` then `b`."  The adjunction says these
are the same question.  The implication `a → b` is the **largest** element
whose meet with `a` is still below `b` — it internalizes the notion of
"assuming `a`, what's the strongest conclusion that stays within `b`?"

**Intuition for the Heyting implication.**

In a Boolean algebra, implication is derived: `a → b ≡ ¬a ∨ b` — "either
`a` is false, or `b` is true."  This is a static truth value: you evaluate
it by checking two conditions.

In a Heyting algebra, `a → b` is a **first-class element** of the algebra,
not a derived expression.  It has its own identity: the set of all
situations where knowing `a` is enough to conclude `b`.  The difference
from Boolean implication matters when the domain has hidden structure
(abstract types, observability boundaries, partial information) where
`¬a` is not the full complement of `a`.

**Practical examples in Rholang guard predicates:**

| Heyting implication                             | Read as                                                                   | Guard application                                                                                                     |
|-------------------------------------------------|---------------------------------------------------------------------------|-----------------------------------------------------------------------------------------------------------------------|
| `reachable(x, A) → reachable(x, B)`             | "If `x` can reach `A`, then `x` can reach `B`"                            | Guard subsumption: every process reaching `A` also reaches `B` — meaning a guard on `B` is weaker than a guard on `A` |
| `isEmpty(stack) → safe(stack)`                  | "If the stack is empty, then it is safe"                                  | Interface-based reasoning: emptiness implies safety (no underflow risk)                                               |
| `valid(token) → authorized(token)`              | "Given validity, produce authorization"                                   | Resource transformation: the validity proof is consumed to produce authorization (see §6, use case #5)                |
| `distinguishable(x, P) → distinguishable(x, Q)` | "If `x` is distinguishable from `P`, then it is distinguishable from `Q`" | Bisimulation refinement: `Q` is harder to distinguish from than `P`                                                   |

The guard subsumption use case is particularly important for the compile-time
pipeline: if `φ → ψ` is a tautology (`φ → ψ = ⊤`), then guard `ψ` is
subsumed by guard `φ` — every value satisfying `φ` also satisfies `ψ`.
In a Boolean algebra this reduces to `SAT(φ ∧ ¬ψ) = false`; in a Heyting
algebra the implication provides the answer directly without requiring the
complement `¬ψ` (which may be imprecise for non-Boolean domains).

The **pseudo-complement** of `a` is defined as:

    ¬a  ≝  (a → ⊥)

which is the largest element disjoint from `a`: `a ∧ ¬a = ⊥`.  Intuition:
`¬a` is the strongest statement that is consistent with `a` being false —
but it may be weaker than the "true" negation because it cannot assert
anything about the boundary between `a` and "not `a`."

**Hierarchy of algebraic structures:**

| Structure            | Operations         | Holds                                                     | Example                           |
|----------------------|--------------------|-----------------------------------------------------------|-----------------------------------|
| Lattice              | `∧, ∨`             | Absorption, idempotence                                   | Power set under ∪, ∩              |
| Distributive lattice | `∧, ∨`             | Distributivity: `a ∧ (b ∨ c) = (a ∧ b) ∨ (a ∧ c)`         | Ideals of a commutative ring      |
| Heyting algebra      | `∧, ∨, →, ¬, ⊥, ⊤` | Adjunction: `a ∧ c ≤ b ⟺ c ≤ (a → b)`                     | Open sets of a topological space  |
| Boolean algebra      | `∧, ∨, ¬, ⊥, ⊤`    | Excluded middle: `a ∨ ¬a = ⊤`; Double negation: `¬¬a = a` | Power set; `BooleanAlgebra` trait |

Every Boolean algebra is a Heyting algebra (with `a → b ≝ ¬a ∨ b`).  The
converse fails: a Heyting algebra may lack the law of excluded middle.

**Birkhoff's representation theorem** (for finite distributive lattices):
every finite distributive lattice is isomorphic to the lattice of
downward-closed sets of a finite poset.  This provides a concrete model:
if MeTTaIL's guard predicates form a finite poset (ordered by implication),
the Heyting algebra of downward-closed sets gives the predicate algebra.

## 2. Double-Negation Closure: Formal Properties

**Theorem (Double-Negation Closure).** In any Heyting algebra `H`, the
operator `¬¬ : H → H` is a **closure operator**:

1. **Extensive:** `a ≤ ¬¬a` for all `a ∈ H`
2. **Monotone:** `a ≤ b ⟹ ¬¬a ≤ ¬¬b`
3. **Idempotent:** `¬¬(¬¬a) = ¬¬a`

*Proof sketch.*
(1) From the adjunction with `c = a`: `a ∧ a ≤ a` (trivially), so
`a ≤ (a → a) = ⊤`.  More precisely: `a ∧ ¬a = ⊥ ≤ ⊥`, so
`a ≤ (¬a → ⊥) = ¬¬a`.
(2) If `a ≤ b`, then `¬b ≤ ¬a` (contravariance of `¬`), so
`¬¬a ≤ ¬¬b` (applying contravariance twice).
(3) From (1): `¬¬a ≤ ¬¬(¬¬a)`.  For the reverse: `¬a ∧ ¬¬a = ⊥`, so
`¬¬a ≤ (¬a → ⊥) = ¬¬a` is just reflexivity after unfolding.  The key
step: `¬(¬¬a) = ¬a` (triple negation reduces to single), so
`¬¬(¬¬a) = ¬(¬(¬¬a)) = ¬(¬a) = ¬¬a`.  □

**The Boolean core.** The set of **regular elements** (also called
**dense elements**) of a Heyting algebra --

    H_reg = { a ∈ H | ¬¬a = a }

-- forms a **Boolean algebra** under the inherited operations.  This is
exactly what the `BooleanApproximation` bridge extracts: it projects every
Heyting predicate into the Boolean core via `¬¬`.

## 3. Topological Semantics: Stone and Esakia Duality

A **duality** in mathematics is a systematic correspondence between two
different kinds of structures — typically an algebraic structure and a
geometric/topological space — where properties and theorems about one
translate mechanically into properties and theorems about the other.  The
value of a duality is that hard algebraic questions may become easy geometric
questions (or vice versa).

**Stone duality** (1937) establishes that every Boolean algebra corresponds
to a unique **Stone space** — a topological space that is compact (every open
cover has a finite subcover), totally disconnected (no connected subsets
beyond single points), and Hausdorff (distinct points have disjoint
neighborhoods).  The elements of the Boolean algebra correspond to the
**clopen** sets of the Stone space — sets that are simultaneously open AND
closed.

**Intuition.** A clopen set has no boundary: the "true" region and the
"false" region are cleanly separated with no ambiguous points between them.
This is exactly what Boolean complement gives you — `¬φ` is the crisp
complement of `φ`, with no boundary cases.  Every Boolean predicate
partitions the space into "definitely true" and "definitely false" with
nothing in between.

**Esakia duality** (1974) extends Stone duality to Heyting algebras.  Every
Heyting algebra corresponds to a unique **Esakia space** — a Stone space
equipped with an additional structure: a **closed partial order** `≤`.  The
elements of the Heyting algebra correspond to the **open upsets** — sets
that are both open (topologically) and upward-closed (if `x ∈ U` and
`x ≤ y`, then `y ∈ U`).

**Intuition.** The partial order encodes an **information ordering**: `x ≤ y`
means "y has at least as much information as x."  An open upset is a property
that, once confirmed at some level of information, remains confirmed at all
higher levels — learning more can confirm the property but never revoke it.
This is the mathematical formalization of why observable properties (those
confirmable in finite observations) form a Heyting algebra: once you've
observed that a process can output 42, additional observations can't undo
that fact.

The key difference from Stone duality: in an Esakia space, open sets may
**not** be clopen.  The complement of an open set is closed, not necessarily
open.  This is why the Heyting pseudo-complement `¬φ` (the interior of the
complement) is weaker than the Boolean complement — it loses the boundary
points that are in the closure but not the interior.

```
  Algebraic side                    Topological side
  ──────────────                    ────────────────
  Boolean algebra          ⟷        Stone space (compact, 0-dim, Hausdorff)
  Heyting algebra          ⟷        Esakia space (Stone + closed partial order)
  Predicate φ              ⟷        Open upset U_φ
  ¬φ (pseudo-complement)   ⟷        int(complement(U_φ))
  ¬¬φ (regularization)     ⟷        int(cl(U_φ))  (interior of closure)
  Regular element (¬¬a=a)  ⟷        Regular open set (int(cl(U)) = U)
  Boolean core H_reg       ⟷        Regular open algebra of the space
```

**Why this matters for MeTTaIL.** The duality explains two things:

1. *Why `¬¬φ` fills gaps:* the closure `cl(U)` adds boundary points (values
   that are "on the edge" of satisfying `φ`), and the interior `int(cl(U))`
   removes the outermost boundary but preserves the filled interior.  The
   result is a **regular open set** — an open set that equals the interior of
   its own closure (`int(cl(U)) = U`), meaning it has no "thin cracks" or
   "missing points."  Regular open sets are exactly the elements of the
   **Boolean core** of the Heyting algebra — the predicates for which
   `¬¬φ = φ`.  This is the `BooleanApproximation` bridge in topological terms.

2. *Why Heyting algebras model observable properties:* open sets in the
   Esakia space are exactly the finitely confirmable properties — those
   where a finite observation suffices to confirm membership.  The partial
   order ensures monotonicity: once confirmed, always confirmed.

## 4. Graph Analysis Examples

**Example 1: Process graph reachability (from main document §11.3, expanded).**

The processes of a rho-calculus system form a partial order under the
subprocess relation: `P ≤ Q` iff `P` is a structural component of `Q`.
The upward-closed sets of this ordering form a Heyting algebra.

- `φ` = `reachable(x, target)`: the set of processes from which `target` is
  reachable via a **demonstrated** finite path — an execution has been
  observed (or can be constructed) that delivers a message from `x` to
  `target`.
- `¬φ` = processes from which `target` is **provably unreachable** — no
  scheduling policy, no sequence of nondeterministic choices, can produce a
  path.
- `¬¬φ` = processes from which `target` is **reachable in the limit** —
  mathematically, the topological closure of the reachable set (including
  boundary/limit points of converging sequences of reachable processes).
  In practice, this means: there exists some consistent sequence of
  nondeterministic choices that would produce a path, even if no single
  finite execution has demonstrated it yet.

**What "reachable in the limit" means in practice.**  Consider a
load-balancing process in Rholang:

```rholang
contract loadBalancer(@msg, ret) = {
  for (@workers <- workerPool) {
    // Nondeterministic: picks a worker based on current load
    match selectLeastLoaded(workers) {
      chosen => {
        chosen!(msg) |
        workerPool!(updateLoad(workers, chosen))
      }
    }
  }
}
```

Three workers — `workerA`, `workerB`, `workerC` — are in the pool.  The
question: "can `workerC` receive a message sent to the load balancer?"

- `reachable(lb, workerC)` might be **false in any specific observed
  execution** — if the scheduler has so far always picked `workerA` or
  `workerB`, no finite observation shows a path to `workerC`.
- But `reachable(lb, workerC)` is **true under some scheduling policies** —
  if the load balancer happens to pick `workerC` next time (which is
  possible but hasn't been demonstrated).
- `¬¬(reachable(lb, workerC))` = **true** — the regularization captures
  "reachable under some consistent nondeterministic choices" even though
  no single finite execution has demonstrated the path yet.

The gap `¬¬φ ∖ φ` contains processes where reachability depends on
**nondeterministic choices that haven't been resolved yet** — the target is
reachable in principle (there exists a valid schedule) but no concrete
execution has demonstrated it.  This is not about infinite chains of
distinct channels; it is about **branching over unbounded nondeterminism**
in real concurrent systems.

**Why this matters for guard dispatch.** A guard like
`for (@msg <- ch) where reachable_closure(msg, service)` accepts messages
that *can* reach the service under some valid scheduling — even if the
current execution hasn't demonstrated that particular path.  This is
important for routing in nondeterministic networks: the guard should not
reject a message just because the specific execution path to the service
hasn't been observed yet.

**Example 2: Bisimulation quotient.**

**Bisimulation** is a central concept in process algebra: two processes `P`
and `Q` are **bisimilar** if they can mimic each other's observable behavior
step by step.  Formally, a bisimulation is a relation `R` such that whenever
`P R Q`:

- If `P` can perform action `a` to become `P′`, then `Q` can perform the
  same action `a` to become some `Q′` with `P′ R Q′`.
- Symmetrically: if `Q` can do `a` to become `Q′`, then `P` can match it.

**Intuition.** From the outside — observing only the sequence of actions
(inputs and outputs) — bisimilar processes are indistinguishable.  They
"look the same" to any finite experiment.  No matter what you ask them to
do, they produce the same observable responses.

**Why bisimulation forms a Heyting algebra.** The key asymmetry:
*distinguishing* two processes is finitely observable (find one experiment
where they respond differently — a finite witness), but *proving
bisimilarity* requires checking ALL possible experiments — an inherently
infinite task.  This asymmetry is precisely the open/closed distinction in
topology:

- Open sets = "observably distinguishable" properties — confirmable in
  finite observations (find the distinguishing experiment)
- Closed sets = "indistinguishable" properties — only refutable (not
  confirmable) in finite observations

The observable properties of processes under bisimulation form a topology
whose open sets constitute a Heyting algebra.

In this topology:
- `φ` = `distinguishable_from(P)`: processes that are observably different
  from `P` in finitely many steps.
- `¬φ` = processes indistinguishable from `P` by any finite observation
  (but possibly distinguishable by infinite observation).
- `¬¬φ` = processes that are either distinguishable or on the boundary of
  distinguishability.

A guard `for (@x <- ch) where bisimilar(x, P)` in this Heyting algebra
asks: "does this process behave identically to `P`?"  This is a genuinely
non-Boolean question — the boundary between "bisimilar" and "distinguishable"
is topologically meaningful, and Boolean complement (which would claim a
crisp partition) cannot faithfully represent it.

**Example 3: Channel connectivity.**

In a Rholang network, processes may forward messages between channels:

```rholang
for (@x <- ch1) { ch2!(x) }    // forwarder: ch1 → ch2
```

The **connectivity closure** of a channel `ch` is the set of channels
reachable from `ch` through arbitrary chains of forwarders -- including
infinite chains.  This forms a Heyting algebra:

- `φ` = `connected(ch, target)`: target is reachable from ch via a finite
  chain of forwarders.
- `¬¬φ` = target is in the **connectivity closure**: reachable via finite
  chains or as a limit of increasingly long chains.

A guard `for (@msg <- ch) where connectivity_closure(ch, target)` checks
whether the channel network can eventually deliver to `target` -- a property
that includes infinite forwarding chains.

## 5. Connection to Intuitionistic Type Theory

The **Curry-Howard correspondence** is a deep structural parallel between
logic and computation: **propositions are types**, **proofs are programs**,
and **proof verification is type checking**.  It is not a metaphor — it is a
precise, mechanical translation where every logical operation has a
computational counterpart and vice versa.

**Intuition.** A proof of "A implies B" is *literally* a function from A to
B — a program that accepts evidence of A as input and produces evidence of B
as output.  Verifying the proof is the same operation as type-checking the
program: if the function has type `A → B`, then it correctly transforms
any A-evidence into B-evidence.

The correspondence maps Heyting algebra operations to type-theoretic
operations:

| Logic (Heyting algebra) | Types                   | Computationally                                     |
|-------------------------|-------------------------|-----------------------------------------------------|
| `φ ∧ ψ`                 | Product type `(A, B)`   | A pair of witnesses — evidence for both             |
| `φ ∨ ψ`                 | Sum type `Either<A, B>` | Evidence for one disjunct (tagged)                  |
| `φ → ψ`                 | Function type `A → B`   | A program transforming A-evidence into B-evidence   |
| `¬φ = (φ → ⊥)`          | `A → Void`              | A program showing A-evidence leads to contradiction |
| `⊥`                     | `Void` (empty type)     | No program can produce a value of this type         |
| `⊤`                     | `()` (unit type)        | Trivially produced (no information needed)          |

**Why Heyting, not Boolean.** Heyting algebras are the algebraic semantics
of **constructive logic** — logic where proofs must be computable.  Boolean
algebras add the **law of excluded middle** (`φ ∨ ¬φ = ⊤`), which asserts
that every proposition is either true or false — but constructive logic
rejects this because it claims existence without providing a construction.
In type-theoretic terms: there is no general program of type
`Either<A, (A → Void)>` — you can't always decide whether a type is
inhabited without actually constructing an inhabitant.

The absence of `¬¬φ = φ` in Heyting algebras corresponds to the absence
of **double-negation elimination** in constructive logic: knowing that `φ`
is not provably false (i.e., every attempt to disprove `φ` leads to
contradiction) does not constructively produce a proof of `φ`.  You know
`φ` "should" be true, but you don't have the actual evidence.

**MeTTaIL connection:** A Heyting predicate on a guard has a natural
computational interpretation: the witness is a *constructive proof* that the
value satisfies the guard.  For `φ → ψ` (guard implication), the witness is
a function transforming any proof of `φ` into a proof of `ψ` -- exactly the
guard subsumption operation from §2.3 of the main document, but now with a
constructive computational content.

This means Heyting guards could carry **proof terms** at runtime: not just
"does the value satisfy the guard?" (Boolean) but "here is the witness
proving it satisfies the guard" (constructive).  This is relevant for
**certified communication** in **high-assurance systems** — systems where
correctness is not merely tested but *proven*, such as avionics, medical
devices, financial settlement, and cryptographic protocols.  In certified
communication, a message on a channel carries not just a value but a
machine-checkable proof that the value satisfies the channel's contract.
The receiver can verify the proof without trusting the sender's
implementation — only the proof's validity matters.  Heyting guards provide
the algebraic foundation for this: the proof term IS the guard witness, and
the Curry-Howard correspondence ensures that a well-typed proof term is a
correct proof.

## 6. What Heyting Algebras Enable That Boolean Algebras Cannot

The previous sections establish the theory.  This section provides concrete
MeTTaIL use cases where Heyting algebras are **necessary** — where Boolean
algebras are structurally unable to express the guard predicate.

**1. Constructive guard witnesses with proof terms.**

Boolean guards answer a binary question: does the value satisfy `φ`?  The
answer is yes or no, with an optional witness (a concrete satisfying element).
But the witness carries no *explanation* of why it satisfies the guard.

Heyting guards, via the Curry-Howard correspondence (§5), can carry
**proof terms** — computational evidence of satisfaction.  The Heyting
implication `φ → ψ` is not just "if `φ` then `ψ`" but "here is a function
that transforms any proof of `φ` into a proof of `ψ`."

```rholang
// Boolean guard: value accepted, but no evidence of why
for (@x <- ch) where safe(x) { P }

// Heyting guard (proposed): value accepted WITH a proof witness
for (@x, @proof <- certified_ch) where safe(x) ∧ certifies(proof, x) { P }
```

In the Heyting version, `certifies(proof, x)` is a constructive predicate:
the proof term `proof` is a concrete derivation showing that `x` is safe.
The Comm rule fires only if the proof checks out — and the proof is then
available to the continuation `P` for further reasoning.  This enables
**certified communication**: a channel that carries not just data but
evidence of its validity.

**Why Boolean algebras cannot do this:** Boolean `SAT(φ)` returns a witness
element `d ∈ ⟦φ⟧`, but the witness is just a value — it has no internal
structure.  The Heyting implication `φ → ψ` produces a *function* (proof
transformer), not a point.  There is no Boolean analog of "a function from
proofs of `φ` to proofs of `ψ`."

**2. Topological closure: properties that hold "in the limit."**

Many process-algebraic properties hold for infinite behaviors but not any
finite prefix.  The classical example: **fairness** ("every enabled action is
eventually executed") requires infinite observations to confirm.  The set of
fair executions is a `G_δ` set (countable intersection of open sets) — not
open, not closed, and the distinction between "finitely confirmable" and
"true in the limit" is precisely the gap between `φ` and `¬¬φ`.

```rholang
// Boolean: can only check finite reachability
for (@x <- ch) where reachable(x, target) { P }

// Heyting (proposed): checks closure of reachability
for (@x <- ch) where reachable_closure(x, target) { P }
```

The Boolean guard `reachable(x, target)` checks whether `target` is
reachable from `x` via a finite path.  The Heyting guard
`reachable_closure(x, target)` checks whether `target` is in the
**topological closure** of the reachable set — including processes that
converge to reachability through infinite chains.

The difference is the regularization: `¬¬(reachable) ⊇ reachable`.  The
gap `¬¬(reachable) ∖ reachable` contains processes that are "reachable in
the limit" — an inherently topological notion that Boolean complement
(which is involutive) cannot distinguish from finite reachability.

**Why Boolean algebras cannot do this:** In a Boolean algebra, `¬¬φ = φ` —
there is no gap between `φ` and its closure.  The distinction between
"finitely confirmable" and "true in the limit" collapses.

**3. Monotone guards over partial information.**

In a concurrent system, processes often have **incomplete knowledge** of the
global state.  A process may know that certain channels are active but not
know the status of others.  Guard predicates over partial information are
naturally **monotone**: learning more information can confirm a guard but
never revoke it (once you know something is safe, additional information
doesn't make it unsafe).

```rholang
// Boolean: requires complete information to evaluate
for (@state <- ch) where globally_safe(state) { P }

// Heyting (proposed): evaluable with partial information
for (@partial_state <- ch) where safe_given_info(partial_state) { P }
```

The Heyting guard `safe_given_info(partial_state)` holds when the partial
state is consistent with safety.  The double negation
`¬¬(safe_given_info)` means "safe in every consistent completion of the
partial information" — a stronger property that is decidable over the
Boolean core.

**Why Boolean algebras cannot do this:** Boolean predicates require the input
to be fully determined — `EVAL(φ, d)` needs a concrete `d ∈ D`.  Heyting
predicates over partial information evaluate over **filters** (upward-closed
consistent sets of partial observations), which form a Heyting algebra but
not a Boolean algebra.

**4. Open-set semantics for observable properties.**

In process algebra, **observable properties** are those confirmable in finite
observations: "the process can output 42" is observable (observe the output),
but "the process never outputs 42" is not (you'd need infinite observation
to confirm it).

The observable properties of a process form a **topology** — the open sets.
And the open sets of a topology form a Heyting algebra.  The pseudo-complement
`¬φ` = "the largest observable property disjoint from `φ`" — which is the
interior of the complement, not the full complement.

```rholang
// Boolean guard: requires checking a non-observable property
for (@x <- ch) where never_deadlocks(x) { P }
    // never_deadlocks is NOT observable — it's a safety property
    // requiring infinite observation to confirm

// Heyting (proposed): checks the observable approximation
for (@x <- ch) where observably_live(x) { P }
    // observably_live is observable — confirmable in finite steps
    // ¬¬(observably_live) ⊇ observably_live captures the closure
```

The Boolean guard `never_deadlocks(x)` requires checking a co-observable
(closed, not open) property — impossible to confirm in finite observations.
The Heyting guard `observably_live(x)` is an open-set predicate:
confirmable in finite steps.  The regularization `¬¬(observably_live)`
captures the closure — processes that are "almost observably live" in the
topological sense.

**Why Boolean algebras cannot do this:** Boolean complement turns an
observable (open) property into its full complement, which is closed (not
observable).  This crosses the observability boundary.  Heyting
pseudo-complement stays within the topology: `¬φ` is always open.

**5. Substructural resource guards via Heyting implication.**

The Heyting implication `φ → ψ` has a **resource-sensitive** interpretation
that has no Boolean analog.  To understand what "consuming `φ` to produce
`ψ`" means, consider a concrete analogy:

**Intuition: the movie ticket.** A movie ticket is a proof of "I paid for
this showing."  At the theater door, the ticket is **consumed** — torn,
scanned, invalidated — to produce entry (a proof of "I'm authorized to be
in this theater").  After use, the ticket is gone: you have the entry
authorization, but you no longer have the ticket.  You cannot use the same
ticket twice.  The ticket was the *input* to a function (the door scanner),
and the entry authorization was the *output*.  The function consumed its
input.

In type-theoretic terms (via the Curry-Howard correspondence, §5): the
Heyting implication `φ → ψ` is a **function** from proofs of `φ` to proofs
of `ψ`.  In a **linear** or **affine** type system — where values must be
used exactly once (linear) or at most once (affine) — calling this function
**consumes** its argument.  The proof of `φ` is the function's input; after
the call, only the output (proof of `ψ`) remains.  The proof of `φ` is no
longer independently available — it was consumed as fuel for the
transformation.

```rholang
// Boolean: guard has no resource sensitivity
for (@token <- ch) where valid(token) { consume(token) }
    // valid(token) is a stateless check — evaluating the guard
    // doesn't use up the token.  The token still exists after
    // the guard fires.

// Heyting (proposed): guard implication consumes the validity proof
for (@token <- ch) where (valid(token) → authorized(token)) { use(token) }
    // The implication is a function: it takes the validity proof
    // as input and produces an authorization proof as output.
    // On a linear channel, the validity proof is consumed — after
    // the guard fires, only the authorization proof remains.
    // The token's validity has been "spent" to obtain authorization.
```

The rho-calculus naturally supports this semantics via **linear channels**:
reading a message from a linear channel consumes it (the message is gone
after the read).  The Heyting implication `valid(token) → authorized(token)`
models this consumption: the validity witness is read (consumed) from the
channel, and the authorization witness is produced in its place.

**Why Boolean algebras cannot do this:** In Boolean algebra,
`φ → ψ ≡ ¬φ ∨ ψ` — the implication is equivalent to a disjunction.  A
disjunction is a **static truth**: "either `φ` is false, or `ψ` is true."
There is no function, no input, no output, no consumption — just a logical
relationship between truth values.  You cannot "call" a disjunction or
"feed it an argument."

The Heyting implication is genuinely different: it is not a derived
operation but the **right adjoint of conjunction** — the largest element `c`
such that `φ ∧ c ≤ ψ`.  The adjunction `a ∧ c ≤ b ⟺ c ≤ (a → b)` gives
`→` its function-like behavior: it internalizes the process of "assuming `a`
and deriving `b`" as a first-class element of the algebra.

**Summary of capabilities beyond Boolean algebras:**

| Capability                             | Boolean                        | Heyting                          | Example guard                       |
|----------------------------------------|--------------------------------|----------------------------------|-------------------------------------|
| Guard witness with proof term          | Value only                     | Function/derivation              | `certifies(proof, x)`               |
| Topological closure (limit properties) | No (`¬¬φ = φ`)                 | Yes (`¬¬φ ⊇ φ`)                  | `reachable_closure(x, target)`      |
| Partial information guards             | No (needs complete `d`)        | Yes (evaluates on filters)       | `safe_given_info(partial_state)`    |
| Observable property guards             | Crosses observability boundary | Stays within topology            | `observably_live(x)`                |
| Resource-sensitive implication         | `¬φ ∨ ψ` (stateless)           | `φ → ψ` (consumes `φ`)           | `valid(token) → authorized(token)`  |
| Abstract data type guards              | Requires internal access       | Operates on observable interface | `stack.isEmpty()`, `map.size() ≥ 3` |

**6. Abstract data types: the natural Heyting domain.**

The distinction between **algebraic data types** (ADTs defined by
constructors — `Option<T> = None | Some(T)`) and **abstract data types**
(ADTs defined by interface — `Stack` with `push`, `pop`, `isEmpty`) is
precisely the distinction between Boolean and Heyting guard analysis.

An **algebraic data type**'s structure is transparent: the compiler can see
every constructor, pattern-match on internal shape, and enumerate all
possible values.  Guards over algebraic types — `@{App(f, Var(x))}` — have
full Boolean analysis: exact satisfiability, overlap, subsumption, and
exhaustiveness via unification and tree automata.

An **abstract data type**'s structure is hidden behind its interface.  The
compiler can only observe behavior through method calls — `stack.isEmpty()`,
`map.contains(key)`, `queue.size() ≥ 3`.  These **observable properties**
form the open sets of a topology, and open sets form a Heyting algebra:

- `φ` = `isEmpty()` is **observable**: call the method, get an answer in
  finite time.  This is an open set.
- `"never overflows"` is **not observable**: it requires checking every
  future `push` — an infinite observation.  This is a closed set, not open.
- `¬φ` (pseudo-complement) = "observably non-empty" — the strongest
  observable property contradicting `φ`.  This stays within the topology
  (open sets), unlike Boolean complement which would cross into closed sets.
- `¬¬φ` = "not observably non-empty" — weaker than `isEmpty`.  It means
  "no finite observation can prove the stack is non-empty."  This is the
  topological closure: `¬¬φ ⊇ φ`.

```rholang
// Algebraic DT guard: compiler sees constructors → Boolean analysis
for (@{Some(x)} <- option_ch) where x > 0 { P }

// Abstract DT guard: compiler sees interface only → Heyting analysis
for (@stack <- stack_ch) where stack.isEmpty() { P }
```

For the algebraic guard, the compiler can determine exactly which `Option`
values match (those that are `Some(x)` with `x > 0`) — full Boolean
analysis.  For the abstract guard, the compiler cannot inspect the stack's
internal representation; it can only reason about what `isEmpty()` returns
— Heyting analysis via observable properties.

**Compile-time implications:**

| Analysis       | Algebraic DT (constructors visible) | Abstract DT (interface only)              |
|----------------|-------------------------------------|-------------------------------------------|
| Algebra        | `BooleanAlgebra` (exact)            | `HeytingAlgebra` (conservative)           |
| SAT            | Exact                               | Sound via `¬¬` approximation              |
| Overlap        | Exact (unification)                 | Conservative (may over-report)            |
| Subsumption    | Exact (matching)                    | Conservative                              |
| Exhaustiveness | Decidable (tree automata)           | Undecidable; conservative via `¬¬`        |
| Dispatch index | Discrimination tree on constructors | Cascading index on interface observations |

**Why Boolean algebras cannot handle abstract data types:** Boolean
complement requires knowing the full universe of values to compute `¬φ` —
but the abstract type's universe is hidden.  The Boolean complement of
`isEmpty()` would need to enumerate all non-empty internal states, which
the abstraction barrier prevents.  The Heyting pseudo-complement `¬φ`
stays within observables: it's the strongest *observable* property
contradicting `φ`, without requiring internal knowledge.

> **Cross-reference:**
> [Compile-Time Guard Analysis](compile-time-guard-analysis.md) §4 discusses
> the practical analysis algorithms for both algebraic and abstract data
> type guards.

## 7. BooleanApproximation Soundness: Formal Proof

**Theorem (Soundness of BooleanApproximation).** Let `H` be a Heyting
algebra and `φ ∈ H`.  Then:

    SAT(¬¬φ) = false  ⟹  SAT(φ) = false

*Proof.* By extensiveness (§2), `φ ≤ ¬¬φ`, so `⟦φ⟧ ⊆ ⟦¬¬φ⟧`.  If
`⟦¬¬φ⟧ = ∅`, then `⟦φ⟧ ⊆ ∅`, so `⟦φ⟧ = ∅`.  □

**Corollary (Overlap soundness).** For `φ, ψ ∈ H`:

    SAT(¬¬φ ∧ ¬¬ψ) = false  ⟹  SAT(φ ∧ ψ) = false

*Proof.* `¬¬` distributes over `∧` in a Heyting algebra:
`¬¬(φ ∧ ψ) ≤ ¬¬φ ∧ ¬¬ψ`.  Combined with `φ ∧ ψ ≤ ¬¬(φ ∧ ψ)`, we get
`φ ∧ ψ ≤ ¬¬φ ∧ ¬¬ψ`.  Apply the same argument as the theorem.  □

**Incompleteness.** The converse does not hold: `SAT(¬¬φ) = true` does not
imply `SAT(φ) = true`.  The gap consists of "boundary elements" -- values
in `⟦¬¬φ⟧ ∖ ⟦φ⟧`.  For practical purposes, this means the
`BooleanApproximation` may produce false positives (reporting a guard as
satisfiable when it is not) but never false negatives (missing a genuinely
satisfiable guard).

For dead guard detection, false positives mean some dead guards go
undetected -- they are reported as "possibly satisfiable."  For overlap
detection, false positives mean some disjoint guards are reported as
"possibly overlapping."  Both directions are conservative (safe) -- no
incorrect code is generated.

## 8. Connection to Lattice Automata

Le Gall & Jeannet (2007) introduce **lattice automata** -- automata over
elements of an atomic lattice.  Transitions are labeled with lattice
elements, and the language is defined by the lattice ordering.

**Comparison with SFAs over Heyting algebras:**

| Property        | SFA (Boolean backend)      | Lattice automata     | SFA (Heyting backend via ¬¬)          |
|-----------------|----------------------------|----------------------|---------------------------------------|
| Alphabet        | Boolean algebra predicates | Lattice elements     | Heyting algebra predicates            |
| Closure under ∩ | ✓ (product)                | ✓                    | ✓ (via ¬¬ approximation)              |
| Closure under ¬ | ✓ (determinize + flip)     | ✗                    | ≈ (pseudo-complement, not involutive) |
| Minterms        | ✓                          | N/A                  | ≈ (via Boolean core H_reg)            |
| Determinization | ✓                          | ✗ (no complement)    | ≈ (via ¬¬ minterms)                   |
| Widening        | N/A                        | ✓ (lattice widening) | Possible (via closure operator)       |

The key insight: lattice automata use **widening operators** to approximate
analysis of infinite-state systems.  The double-negation closure `¬¬` in a
Heyting algebra is a natural widening operator -- it over-approximates the
predicate by filling gaps.  This suggests a convergence between the Heyting
approach and the lattice automata approach.

## 9. Potential Rust Implementation Architecture

The `HeytingAlgebra` trait would extend the existing trait hierarchy:

```rust
/// A Heyting algebra: a bounded distributive lattice with implication.
/// Every BooleanAlgebra is a HeytingAlgebra (with implies = or(not(a), b)).
pub trait HeytingAlgebra: Clone + Debug + Send + Sync + 'static {
    type Predicate: Clone + Debug + Eq + Hash + Send + Sync + 'static;
    type Domain: Clone + Debug + Send + Sync + 'static;

    fn true_pred(&self) -> Self::Predicate;
    fn false_pred(&self) -> Self::Predicate;
    fn and(&self, a: &Self::Predicate, b: &Self::Predicate) -> Self::Predicate;
    fn or(&self, a: &Self::Predicate, b: &Self::Predicate) -> Self::Predicate;
    fn implies(&self, a: &Self::Predicate, b: &Self::Predicate) -> Self::Predicate;
    fn pseudo_complement(&self, a: &Self::Predicate) -> Self::Predicate;
    fn is_satisfiable(&self, a: &Self::Predicate) -> bool;
    fn evaluate(&self, pred: &Self::Predicate, elem: &Self::Domain) -> bool;

    /// Double-negation closure: ¬¬a. The best Boolean approximation of a.
    fn regularize(&self, a: &Self::Predicate) -> Self::Predicate {
        self.pseudo_complement(self.pseudo_complement(a))
    }
}

/// Lifts a HeytingAlgebra to a BooleanAlgebra via double-negation closure.
/// Sound but incomplete: SAT(¬¬φ)=false ⟹ SAT(φ)=false (no false negatives).
pub struct BooleanApproximation<H: HeytingAlgebra> {
    inner: H,
}

impl<H: HeytingAlgebra> BooleanAlgebra for BooleanApproximation<H> {
    type Predicate = H::Predicate;
    type Domain = H::Domain;

    fn not(&self, a: &Self::Predicate) -> Self::Predicate {
        self.inner.regularize(self.inner.pseudo_complement(a))
    }

    fn is_satisfiable(&self, a: &Self::Predicate) -> bool {
        self.inner.is_satisfiable(self.inner.regularize(a))
    }

    // and, or, true_pred, false_pred: delegate directly (exact)
    // witness, evaluate: delegate directly
}
```

The `ProductAlgebra` generalization would accept mixed Boolean + Heyting
components:

```rust
/// Product of a BooleanAlgebra and a HeytingAlgebra.
/// The Boolean component provides exact minterms; the Heyting component
/// provides ¬¬-approximate minterms.
pub struct MixedProductAlgebra<B: BooleanAlgebra, H: HeytingAlgebra> {
    boolean: B,
    heyting: BooleanApproximation<H>,
}

impl<B: BooleanAlgebra, H: HeytingAlgebra> BooleanAlgebra
    for MixedProductAlgebra<B, H>
{
    // SAT(Both(b, h)) = SAT_B(b) ∧ SAT_H(¬¬h)
    // Exact on the Boolean side, approximate on the Heyting side.
}
```

## 10. Concrete Pipeline Integration: Compile-Time, Optimization, and Runtime

### 10.1 Data Types That Require Heyting Algebras

Boolean algebras work when the compiler can see the full structure of the
domain — enumerate constructors, compute crisp complements, partition
exhaustively.  Heyting algebras are needed when the domain has **hidden
structure** that the compiler cannot fully inspect.

| Data type                            | Why Boolean fails                                                                     | What Heyting provides                                | Example guard                  |
|--------------------------------------|---------------------------------------------------------------------------------------|------------------------------------------------------|--------------------------------|
| **Abstract DTs** (Stack, Map, Queue) | Complement requires enumerating internal states — hidden by abstraction barrier       | Pseudo-complement `¬φ` stays within observables      | `stack.isEmpty()`              |
| **Graph reachability**               | Crisp reachable/unreachable misses boundary processes reachable only in the limit     | `¬¬(reachable)` = reachability closure               | `reachable_closure(x, target)` |
| **Bisimulation**                     | Distinguishability is open, bisimilarity is closed — Boolean `¬` crosses the boundary | `¬(distinguishable)` stays open                      | `bisimilar(x, P)`              |
| **Partial information**              | Boolean `EVAL` needs fully determined input `d ∈ D`                                   | Evaluates on filters (upward-closed consistent sets) | `safe_given_info(partial)`     |
| **Observable properties**            | Boolean `¬(can output 42)` = "never outputs 42" — crosses from open to closed         | Heyting `¬` stays within open sets                   | `observably_live(x)`           |

### 10.2 How Heyting Algebras Operate on These Types

To make the operations concrete, consider a `ReachabilityAlgebra` where
predicates describe which processes can reach which targets:

| Operation                 | Expression                          | Result                                                                                                                                                                                                                                                                                          |
|---------------------------|-------------------------------------|-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `and`                     | `reachable(x, A) ∧ reachable(x, B)` | Processes that can reach BOTH `A` and `B`                                                                                                                                                                                                                                                       |
| `or`                      | `reachable(x, A) ∨ reachable(x, B)` | Processes that can reach `A` or `B` (or both)                                                                                                                                                                                                                                                   |
| `pseudo_complement` (`¬`) | `¬reachable(x, A)`                  | Processes provably unable to reach `A` — excluding boundary cases where reachability is undetermined                                                                                                                                                                                            |
| `implies` (`→`)           | `reachable(x, A) → reachable(x, B)` | "If `x` can reach `A`, then `x` can reach `B`" — the largest set of processes for which reaching `A` guarantees reaching `B`                                                                                                                                                                    |
| `regularize` (`¬¬`)       | `¬¬reachable(x, A)`                 | The **reachability closure**: mathematically, the topological closure of the reachable set (limit points included).  In practice, processes potentially reachable under some valid nondeterministic scheduling, even if no specific execution has demonstrated the path yet (see §4, Example 1) |
| `is_satisfiable`          | `SAT(reachable(x, A))`              | Does any process `x` exist that can reach `A`?                                                                                                                                                                                                                                                  |

The key difference from Boolean: `¬reachable(x, A)` does NOT mean "cannot
reach A" — it means "provably cannot reach A under any scheduling policy."
The gap `¬¬φ ∖ φ` contains processes whose reachability depends on
**unresolved nondeterministic choices** — valid schedules exist that would
produce a path, but no concrete execution has demonstrated one.

### 10.3 How Heyting Assists Boolean: The BooleanApproximation Bridge

The compile-time pipeline (main document §2.5) has six stages.  Heyting
algebras affect stages 3-6 through the `BooleanApproximation<H>` bridge:

```
╔══════════════════════════════════════════════════════════════════════════╗
║  COMPILE_HEYTING_GUARD(φ : HeytingPred, H : HeytingAlgebra)              ║
║                                                                          ║
║  Compile a Heyting guard predicate into an SFA for analysis.             ║
║                                                                          ║
║  1. approx ← BooleanApproximation::new(H)                                ║
║     ▷ Wraps H; delegates ∧, ∨ exactly; implements ¬ via ¬¬(¬φ)           ║
║                                                                          ║
║  2. φ_reg ← approx.regularize(φ)          ▷ ¬¬φ: Boolean approximation   ║
║                                                                          ║
║  3. sfa ← SymbolicAutomaton::from_pred(φ_reg, &approx)                   ║
║     ▷ Standard SFA construction — works because approx is BooleanAlgebra ║
║                                                                          ║
║  4. return sfa                                                           ║
║     ▷ All SFA operations (minterms, determinization, equivalence) work   ║
║     ▷ Results are conservative: SAT(¬¬φ)=false ⟹ SAT(φ)=false            ║
╚══════════════════════════════════════════════════════════════════════════╝
```

**Stage 4 (Analyze).** The analysis questions use the regularized SFA:

| Analysis    | Operation                     | Soundness                                                |
|-------------|-------------------------------|----------------------------------------------------------|
| Dead guard  | `SAT(¬¬φ) = false`            | **Sound:** if empty, definitely dead → safe to eliminate |
| Overlap     | `SAT(¬¬φᵢ ∧ ¬¬φⱼ) = false`    | **Sound:** if empty, definitely disjoint                 |
| Subsumption | `SAT(¬¬φⱼ ∧ ¬(¬¬φᵢ)) = false` | **Sound:** if covered, definitely shadowed               |

**Stage 5 (Minterms).** Minterm computation uses `BooleanApproximation`.
The minterms partition the domain into regions where the *regularized*
guards behave identically.  Some regions are **exact** (`¬¬φ = φ` for all
guards in the region); others are **boundary** (`¬¬φ ⊋ φ` for some guard).

**Stage 6 (Codegen).** The compiler marks boundary minterms for runtime
re-verification via Ascent.

### 10.4 Compile-Time Optimization

Three concrete gains:

**1. Dead guard elimination for previously-T2 guards.**

Without Heyting algebras, guards over abstract types and graph properties
are classified T2 (runtime-only) — the compiler cannot analyze them.
The `BooleanApproximation` enables T1-like analysis (conservative):

    Before: reachable_closure(x, target) → T2 (runtime only, no analysis)
    After:  ¬¬(reachable_closure(x, target)) → T1-conservative (compile-time)

A guard dead under regularization is definitely dead — eliminated with zero
runtime cost.

**2. Overlap/subsumption warnings for abstract DT guards.**

Two guards `stack.isEmpty()` and `stack.size() ≥ 3` can be checked for
overlap at compile time via their regularizations — previously impossible.

**3. Selective tier promotion.**

Guards with small or empty `¬¬φ ∖ φ` gaps can be promoted from T2 to T1.
The compiler measures the gap (via witness generation on the difference SFA)
and promotes when the approximation is sufficiently precise.

### 10.5 Runtime Dispatch

For Heyting guards, Layer 2 of the runtime dispatch has two phases:

```
  Value v arrives
       │
       ▼
  Phase 2a: Minterm identification (from regularized SFA)
       │    Cost: O(log m) or O(1)
       │
       ├── Exact minterm (¬¬φ = φ for all guards in region):
       │   Result known from minterm table → no further check needed
       │
       └── Boundary minterm (¬¬φ ⊋ φ for some guard):
           │
           ▼
  Phase 2b: Precise Heyting evaluation (Ascent fixpoint lookup)
           │    Cost: O(1) hash lookup
           │    Checks the original (non-regularized) predicate
           │
           ▼
       Guard result
```

Exact minterms skip Phase 2b entirely — same cost as Boolean guards.
Only boundary minterms incur the Ascent lookup.

### 10.6 Mixed-Domain: Boolean + Heyting

For `x ≥ 10 ∧ reachable_closure(x, target)`, the
`MixedProductAlgebra<IntervalAlgebra, ReachabilityAlgebra>` decomposes:

- **Boolean side** (`IntervalAlgebra`): exact minterms, full SFA analysis,
  `O(log m)` segment tree dispatch
- **Heyting side** (`ReachabilityAlgebra` via `BooleanApproximation`):
  approximate minterms, conservative analysis, boundary cases fall to Ascent

Cascade ordering (main document §7.1) evaluates the most selective
component first.

### 10.7 Bisimulation: The Central Use Case

Identifying **bisimilar processes** is a major goal of MeTTaIL.  Heyting
algebras, SFAs, and Ascent each contribute a distinct layer to this goal.

**Why bisimulation matters:**

- **Optimization:** Replace a complex process with a simpler bisimilar one
- **Verification:** Prove an implementation is bisimilar to its specification
- **Garbage collection:** Processes bisimilar to the null process can be
  eliminated
- **Guard dispatch:** Guards like `where behaves_like(x, spec)` need
  bisimulation analysis

**The asymmetry that makes bisimulation Heyting.**

Two processes are **bisimilar** if no finite experiment can distinguish them
(§4, Example 2).  The critical asymmetry:

- **Distinguishing** is finitely observable: find ONE experiment where the
  processes respond differently.  This is an **open** property.
- **Proving bisimilarity** requires checking ALL possible experiments — an
  infinite task.  This is a **closed** property.

Boolean complement would claim `¬(distinguishable) = bisimilar` — but this
crosses from open to closed, violating the topological structure.  Heyting
pseudo-complement gives `¬(distinguishable) =` "not observably
distinguishable" — a weaker but topologically correct statement that stays
within open sets.

**Minterms are not just for integers.**

A common misconception: minterms work over ANY `BooleanAlgebra`, not just
numeric domains.  The definition is purely algebraic — `∧`, `¬`, `SAT` are
the only requirements.  For process properties, minterms partition the
space of processes into equivalence classes where every guard predicate
behaves identically.  This is precisely what bisimulation partition
refinement does — it partitions processes into classes indistinguishable by
any observation.

**SFA integration for bisimulation over arbitrary process types.**

The labeled transition system (LTS) of a process can be modeled as an SFA:

- **States** = process configurations
- **Transitions** = actions (sends/receives in the rho-calculus)
- **Action domain** = names (quoted processes) — an infinite domain
- **SFA guards** = predicates over actions from a `ProcessActionAlgebra`
  (e.g., "any send on a channel whose name quotes a process satisfying `P`")

The SFA representation is **symbolic**: it uses predicates over the infinite
action space rather than enumerating concrete actions.  This is what makes
the analysis tractable for the rho-calculus, where the set of possible
actions is as large as the set of all processes.

**Bisimulation via SFA partition refinement.**

For **deterministic** processes, bisimilarity equals SFA language
equivalence — decidable via minimization and isomorphism checking (D'Antoni
& Veanes, 2014).

For **nondeterministic** processes, the classical Paige-Tarjan partition
refinement algorithm is lifted to SFAs:

```
╔══════════════════════════════════════════════════════════════════════════╗
║  SFA_BISIM_PARTITION_REFINE(lts : SFA<ProcessActionAlgebra>)             ║
║                                                                          ║
║  Compute the coarsest bisimulation partition of the process LTS.         ║
║                                                                          ║
║  ── Initialization ────────────────────────────────────────────────────  ║
║                                                                          ║
║  partition ← { Q }                 ▷ all states in one block initially   ║
║                                                                          ║
║  ── Refinement loop ───────────────────────────────────────────────────  ║
║                                                                          ║
║  repeat:                                                                 ║
║      Choose a splitter block B and compute its action minterms:          ║
║      minterms ← compute_minterms(guards on transitions into B)           ║
║      ▷ Minterms partition the INFINITE action space into finitely many   ║
║      ▷ equivalence classes — this is what makes the algorithm terminate  ║
║                                                                          ║
║      for each block C in partition:                                      ║
║          for each minterm m:                                             ║
║              C₁ ← { s ∈ C | ∃ transition s ──m──▶ t ∈ B }                ║
║              C₂ ← C ∖ C₁                                                 ║
║              if C₁ ≠ ∅ and C₂ ≠ ∅:                                       ║
║                  replace C with C₁, C₂ in partition     ▷ split          ║
║                                                                          ║
║  until no block was split                                                ║
║                                                                          ║
║  return partition                                                        ║
║  ▷ States in the same block are bisimilar                                ║
╚══════════════════════════════════════════════════════════════════════════╝
```

The key insight: instead of splitting by concrete actions (impossible —
infinite domain), the algorithm splits by **minterms** of the action
predicates.  Minterms reduce the infinite action space to finitely many
equivalence classes, guaranteeing termination.

**Heyting algebras for abstract-type actions.**

When channel values are abstract data types (the `ProcessActionAlgebra` is
Heyting, not Boolean), the `BooleanApproximation` bridge enables partition
refinement with regularized minterms:

- **Sound:** processes in the same block after refinement are **definitely**
  bisimilar (the regularization can only merge blocks, never split them
  incorrectly)
- **Incomplete:** some truly bisimilar processes may end up in different
  blocks (the regularization may over-distinguish at boundary actions)

**How Ascent closes the remaining gaps at runtime.**

Three specific gaps that SFA + Heyting cannot close at compile time:

**Gap 1: Boundary bisimulation cases (Heyting incompleteness).**

The `¬¬` approximation may report some truly bisimilar processes as
"possibly distinguishable."  At runtime, Ascent resolves these via concrete
fixpoint computation: the `eqrel` annotation on equality relations
iteratively applies congruence rules (`eq_proc(a,b) :- eq_proc(f(a),f(b))`)
until the partition stabilizes.  The converged fixpoint IS the exact
bisimulation — and the `O(1)` hash-indexed lookup resolves each boundary
query.

**Gap 2: Dynamic process structure (compile-time unknowns).**

The SFA analysis operates on guard *patterns* — symbolic representations of
what the programmer wrote.  But the rho-calculus supports reflection:
processes can create new constructors and channel names at runtime that the
compiler never saw.  Ascent handles this because it operates on **concrete
terms** at runtime — any structure that arrives is evaluated against the
actual fixpoint.

**Gap 3: Infinite behavioral properties (liveness, fairness).**

Some bisimulation-relevant properties are inherently infinite: "this process
eventually responds to every request" (liveness), "this process treats all
channels fairly" (fairness).  The SFA + Heyting compile-time analysis can
only approximate these.  At runtime, M2 (Weighted Büchi) classifies them
as T3 (bounded check via `LogicT` with depth limit `k`) or T4 (undecidable,
trust wrapper), and the LTL-modulo-𝒜 construction from Veanes et al. (2023)
provides the compilation strategy.

**The three-layer picture for bisimulation:**

```
  ╔═══════════════════════════════════════════════════════════════════╗
  ║  COMPILE TIME: SFA + Heyting                                      ║
  ║                                                                   ║
  ║  Process LTS ──▶ SFA<ProcessActionAlgebra>                        ║
  ║       │                                                           ║
  ║       ▼                                                           ║
  ║  Partition refinement via regularized (¬¬) minterms               ║
  ║       │                                                           ║
  ║       ▼                                                           ║
  ║  Conservative pre-partition:                                      ║
  ║  ├── Definitely-bisimilar groups → equivalence seeds              ║
  ║  ├── Possibly-distinguishable pairs → flagged for runtime         ║
  ║  └── Liveness properties → classified T3/T4                       ║
  ╚═══════════════════════════╪═══════════════════════════════════════╝
                              │ seeds + flags
  ╔═══════════════════════════╪═══════════════════════════════════════╗
  ║  RUNTIME: Ascent          │                                       ║
  ║                           │                                       ║
  ║  Seed eqrel with ◄────────┘                                       ║
  ║  pre-partition                                                    ║
  ║       │                                                           ║
  ║       ▼                                                           ║
  ║  Fixpoint: congruence + rewrite rules close gaps                  ║
  ║       │                                                           ║
  ║       ├── Boundary cases: resolved by fixpoint (O(1) lookup)      ║
  ║       ├── Dynamic structure: concrete terms evaluated             ║
  ║       └── Liveness: LogicT bounded search (T3)                    ║
  ║                                                                   ║
  ║  Result: exact bisimulation classes                               ║
  ╚═══════════════════════════════════════════════════════════════════╝
```

The compile-time analysis does the heavy lifting (partition refinement over
the infinite action space); the runtime fixpoint closes the gaps on concrete
terms.  Most processes are resolved at compile time — only boundary cases
and dynamic structures require runtime work.

### 10.8 Summary: What Changes vs. Pure Boolean Guards

| Pipeline stage      | Boolean guard                        | Heyting guard                                                       | Difference                         |
|---------------------|--------------------------------------|---------------------------------------------------------------------|------------------------------------|
| **Stage 3**         | SFA from `BooleanAlgebra`            | SFA from `BooleanApproximation<H>`                                  | Wraps in `¬¬` bridge               |
| **Stage 4**         | Exact SAT, overlap, subsumption      | Conservative analysis                                               | May miss some dead/disjoint guards |
| **Stage 5**         | Exact domain partition               | Approximate partition with boundary minterms                        | Some regions flagged for runtime   |
| **Stage 6**         | Guard check code                     | Check + boundary fallback to Ascent                                 | Extra branch for boundaries        |
| **Runtime Layer 2** | Single-phase evaluation              | Two-phase: minterm + optional Ascent                                | Exact minterms skip Phase 2b       |
| **Bisimulation**    | Not applicable (Boolean can't model) | Partition refinement via regularized SFA minterms + Ascent fixpoint | New capability                     |

Guards that were previously **invisible to compile-time analysis** (T2
runtime-only) gain conservative but useful optimization — dead guard
elimination, overlap detection, dispatch table construction, and
bisimulation pre-partitioning.  The runtime cost for exact minterms is
identical to Boolean guards; only boundary regions and dynamic structures
pay extra via Ascent.

---

## 11. References

1. Birkhoff, G. (1937). "Rings of sets." *Duke Mathematical Journal*,
   3(3):443-454.

2. Esakia, L. (2019). [*Heyting Algebras: Duality
   Theory*](https://doi.org/10.1007/978-3-030-12096-2). Springer, Trends in
   Logic, vol. 50.

3. Johnstone, P. T. (1982). *Stone Spaces*. Cambridge University Press.
   ISBN: 0-521-23893-5.

4. Le Gall, T. & Jeannet, B. (2007). ["Lattice automata: A representation
   for languages on infinite alphabets, and some applications to
   verification."](https://doi.org/10.1007/978-3-540-74061-2_4) *SAS 2007*,
   LNCS 4634, pp. 52-68. Springer.

5. Martin-Löf, P. (1984). *Intuitionistic Type Theory*. Bibliopolis.
