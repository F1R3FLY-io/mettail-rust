# LogicT Fair Backtracking Search Framework

**Feature gate:** `logict`
**Module:** `prattail/src/logict.rs`
**Dependencies:** none (core infrastructure)

---

## Intuition: Why Fair Search Matters

Consider a naive depth-first backtracking search that explores constraint alternatives:

```
                  root
                 /    \
              left     right
             / | \       |
           l1 l2 l3     r1
          / \
        ...  (infinite)
```

Depth-first search commits to the left branch and descends into `l1`, then `l1`'s children, then their children, potentially forever. If the left subtree is infinite (or just very deep), the right branch is *starved* -- `r1` is never explored, even though it might be the answer we need.

This starvation problem is not hypothetical. In constraint propagation over unbalanced domains -- say, `PresburgerTheory` searching over integer assignments or `UnificationTheory` exploring alternative constructors -- the search tree can be highly asymmetric. A constraint like `x + y <= 100 /\ x >= 0 /\ y >= 0` has 5,151 solutions; naive depth-first search by `x` would enumerate all 101 values of `x` (and for each, all valid `y` values) before considering any alternative decomposition.

LogicT solves this with **fair disjunction**: the `interleave` operation alternates between branches, guaranteeing that both sides of any disjunction are explored infinitely often. No branch can be starved, regardless of the tree shape.

---

## Theory: The msplit Primitive

LogicT originates from Kiselyov, Shan, Friedman & Sabry's 2005 ICFP paper, which identified `msplit` as the fundamental primitive from which all other search operations can be derived.

### Definition

`msplit` deconstructs a search stream into its first result and the remainder:

```
msplit : LogicStream<T> → Option<(T, LogicStream<T>)>
```

- If the stream has results, returns `Some((first, rest))`.
- If the stream is exhausted, returns `None`.

This is analogous to pattern matching on a list (`head :: tail`), but for a potentially lazy, branching computation.

### All Eight Operations

Every LogicT operation is defined in terms of `msplit`:

| Operation | Signature | Semantics |
|-----------|-----------|-----------|
| `mzero()` | `() -> LogicStream<T>` | Empty stream (failure). Identity for `mplus` and `interleave`. |
| `unit(v)` | `T -> LogicStream<T>` | Singleton stream containing `v`. |
| `msplit()` | `LogicStream<T> -> Option<(T, LogicStream<T>)>` | Peek at first result + remainder. The fundamental primitive. |
| `mplus(a, b)` | `(LogicStream, LogicStream) -> LogicStream` | Concatenation (**unfair**). All of `a` before any of `b`. |
| `interleave(a, b)` | `(LogicStream, LogicStream) -> LogicStream` | Fair disjunction. Alternates branches from `a` and `b`. |
| `fair_conjoin(f)` | `(LogicStream<T>, T -> LogicStream<U>) -> LogicStream<U>` | Fair conjunction (>>-). Applies `f` to each result, interleaves all outputs. |
| `ifte(test, then, else)` | `(LogicStream<T>, T -> LogicStream<U>, LogicStream<U>) -> LogicStream<U>` | Soft cut. If `test` succeeds, apply `then`; otherwise use `else`. |
| `once()` | `LogicStream<T> -> LogicStream<T>` | Hard cut. Commit to first result only. |
| `gnot()` | `LogicStream<T> -> LogicStream<()>` | Negation as finite failure. Succeeds iff stream is empty. |

### Formal Signatures with Pre/Post Conditions

**msplit**
```
Pre:  stream is a valid LogicStream (finite or infinite branching)
Post: if stream has >= 1 result, returns Some((first, rest))
        where first is the earliest available result
        and rest is a valid LogicStream containing all remaining results
      if stream is exhausted, returns None
```

**interleave**
```
Pre:  a, b are valid LogicStreams
Post: result is a LogicStream such that:
        forall i in N, if a has an i-th result a_i, then a_i appears in result
        forall j in N, if b has a j-th result b_j, then b_j appears in result
        (fairness: both a and b are explored infinitely often)
```

**fair_conjoin**
```
Pre:  stream is a valid LogicStream<T>, f : T -> LogicStream<U>
Post: result = fold(stream.map(f), empty, interleave)
        i.e., f is applied to each result of stream, and all resulting
        streams are interleaved. No single application of f can starve others.
```

---

## Fairness: The Interleave Guarantee

The core fairness property is best understood through an example.

Given streams A = [a1, a2, a3, ...] and B = [b1, b2, b3, ...]:

```
mplus(A, B)       = [a1, a2, a3, ..., b1, b2, b3, ...]   -- UNFAIR
interleave(A, B)  = [a1, b1, a2, b2, a3, b3, ...]         -- FAIR
```

With `mplus`, if A is infinite, B is never reached. With `interleave`, every element of both A and B appears within finite time.

**Theorem (Fairness).** For any two LogicStreams `a` and `b`, `interleave(a, b)` explores both `a` and `b` infinitely often. Formally: for every natural number `n`, there exist indices `i, j <= 2n` such that the `i`-th element of `interleave(a, b)` comes from `a` and the `j`-th comes from `b`.

*Proof sketch.* The VecDeque implementation alternates: push one branch from `a`, then one from `b`, repeating. After `2n` steps, at least `n` elements from each source have been added to the queue. Since each `msplit` call processes the front of the queue, elements from both sources are produced in bounded time.

### Fair Conjunction

`fair_conjoin` extends fairness to the monadic bind (>>-). Without fairness:

```
stream.bind(f) = [f(a1)..., f(a2)..., f(a3)..., ...]
```

If `f(a1)` produces many results, `f(a2)` is starved. With `fair_conjoin`:

```
stream.fair_conjoin(f) = interleave(f(a1), interleave(f(a2), interleave(f(a3), ...)))
```

Results from `f(a1)`, `f(a2)`, `f(a3)`, ... are all interleaved, preventing starvation.

**Example:**
```
stream = [10, 20]
f(x) = [x+1, x+2]

stream.fair_conjoin(f)  = [11, 21, 12, 22]     -- interleaved
naive bind              = [11, 12, 21, 22]     -- depth-first
```

---

## VecDeque Implementation: Why Explicit Queue

The PraTTaIL implementation uses an explicit `VecDeque<Branch<T>>` rather than the CPS/SFKT (success-failure continuation) representation from the original paper. This choice is motivated by:

1. **Stack safety.** CPS-based LogicT can blow the stack with deep searches. The explicit queue keeps all state on the heap, consistent with PraTTaIL's trampoline architecture.

2. **Debuggability.** The `VecDeque` state is inspectable -- you can see how many branches remain, what their types are, and where they came from. CPS closures are opaque.

3. **Memory efficiency.** Branch suspension uses `Box<dyn FnOnce()>` for lazy evaluation, but the queue itself is a flat `VecDeque` with O(1) amortized push/pop. No nested closure chains.

4. **Integration.** The same explicit-stack philosophy powers the trampoline parser (`trampoline.rs`), making the codebase consistent in its approach to recursion elimination.

### Branch Representation

```
enum Branch<T> {
    Ready(T),                                          -- value ready to yield
    Suspended(Box<dyn FnOnce() -> BranchResult<T>>),   -- deferred computation
}

enum BranchResult<T> {
    Yield(T, Vec<Branch<T>>),   -- value + more branches
    Fail,                        -- no result
    Fork(Vec<Branch<T>>),       -- split into sub-branches
}
```

The `msplit` implementation processes branches from the front of the queue:
- `Ready(v)`: return `v` immediately.
- `Suspended(f)`: call `f()`, handle the result:
  - `Yield(v, more)`: return `v`, push `more` to back of queue.
  - `Fail`: skip, continue to next branch.
  - `Fork(branches)`: push all to back, continue.

This round-robin scheduling is what delivers fairness: new branches go to the *back* of the queue, ensuring older branches are processed first.

---

## ConstraintTheory Trait

The `ConstraintTheory` trait is the abstraction that allows any constraint domain to plug into PraTTaIL's symbolic automata framework. It separates two orthogonal concerns:

1. **Propagation** -- deterministic constraint narrowing. Adding a constraint to the store may detect inconsistency (return `None`) or produce a refined store. For decidable theories, this alone suffices.

2. **Labeling** -- non-deterministic search choices. For theories that need search (e.g., choosing among alternative constructor matches), `label()` produces a `LogicStream` of constraint alternatives that LogicT explores fairly.

### Formal Specification

```rust
trait ConstraintTheory: Clone + Debug + Send + Sync + 'static {
    type Constraint: Clone + Debug + Eq + Hash + Send + Sync + 'static;
    type Assignment: Clone + Debug + Send + Sync + 'static;
    type Store: Clone + Debug + Send + Sync + 'static;

    /// Pre:  store is consistent (is_consistent(store) = true)
    /// Post: if Some(s'), then s' is consistent and
    ///       forall assignments a:
    ///         evaluate(c, a) /\ satisfies(store, a)
    ///         iff satisfies(s', a)
    ///       if None, then {store} union {c} is unsatisfiable
    fn propagate(&self, store: &Store, c: &Constraint) -> Option<Store>;

    /// Pre:  true
    /// Post: result = true iff exists assignment a such that satisfies(store, a)
    fn is_consistent(&self, store: &Store) -> bool;

    /// Pre:  is_consistent(store) = true
    /// Post: if Some(a), then satisfies(store, a) = true
    ///       if None, then store needs labeling (or is inconsistent)
    fn witness(&self, store: &Store) -> Option<Assignment>;

    /// Pre:  is_consistent(store) = true
    /// Post: LogicStream of constraints that, when added via propagate,
    ///       enumerate all valid extensions of the store
    ///       For decidable theories: LogicStream::empty()
    fn label(&self, store: &Store) -> LogicStream<Constraint>;

    /// Pre:  true
    /// Post: result = true iff assignment a satisfies constraint c
    fn evaluate(&self, c: &Constraint, a: &Assignment) -> bool;
}
```

### Usage Patterns: label() per Theory Type

| Theory | Decidability | `label()` behavior | Rationale |
|--------|-------------|-------------------|-----------|
| `PresburgerTheory` | Decidable | `LogicStream::empty()` | NFA-based satisfiability determines outcome without search |
| `LatticeTheory` | Decidable | `LogicStream::empty()` | Finite universe: Warshall closure computes all relationships |
| `UnificationTheory` | Decidable | `LogicStream::empty()` (base); `CustomMatch` alternatives (extension) | Core Martelli-Montanari is deterministic; extended patterns may need choice |
| User-defined | Varies | Domain-specific search | Implements `ConstraintTheory`, gets `BooleanAlgebra` for free via `TheoryAlgebra` |

---

## TheoryAlgebra Bridge: ConstraintTheory to BooleanAlgebra

`TheoryAlgebra<T>` wraps any `ConstraintTheory` implementation and provides a `BooleanAlgebra` implementation, enabling integration with `SymbolicAutomaton<TheoryAlgebra<T>>`.

### Architecture

```
                  TheoryAlgebra<T>
                  ┌──────────────────────────────────────────┐
                  │                                          │
                  │   BooleanAlgebra impl                    │
                  │     Predicate = TheoryPred<T>            │
                  │     Domain    = T::Assignment             │
                  │                                          │
                  │   is_satisfiable(pred):                  │
                  │     1. collect_constraints(pred, empty)   │
                  │        → LogicStream<T::Store>            │
                  │     2. For each store in bounded results: │
                  │        a. Try theory.witness(store)       │
                  │        b. Validate witness against pred   │
                  │        c. If valid → return true          │
                  │        d. Try theory.label(store) for     │
                  │           additional search choices       │
                  │     3. If no valid witness → false        │
                  │                                          │
                  │   collect_constraints handles:            │
                  │     True  → unit(store)                   │
                  │     False → empty()                       │
                  │     Atom(c) → propagate(store, c)         │
                  │     And(a,b) → a_stores.fair_conjoin(b)   │
                  │     Or(a,b) → a_stores.interleave(b)      │
                  │     Not(p) → De Morgan push-down          │
                  │                                          │
                  └──────────────────────────────────────────┘
```

### TheoryPred: Boolean Combination of Constraints

`TheoryPred<T>` is the predicate type for `TheoryAlgebra<T>`:

```
TheoryPred<T> ::= True
               |  False
               |  Atom(T::Constraint)
               |  And(TheoryPred, TheoryPred)
               |  Or(TheoryPred, TheoryPred)
               |  Not(TheoryPred)
```

This wraps theory-specific constraints in a standard Boolean AST, enabling the bridge to handle arbitrary Boolean combinations without requiring the underlying theory to support negation or disjunction directly.

### Decidable vs Search Paths

```
  ┌──────────────────────────────────────────┐
  │          is_satisfiable(pred)             │
  │                                          │
  │   collect_constraints(pred, empty_store)  │
  │           │                              │
  │           ▼                              │
  │   LogicStream<Store>                     │
  │           │                              │
  │     ┌─────┴──────┐                       │
  │     │ Decidable  │  label() = empty()    │
  │     │ (Presburger│  witness() suffices    │
  │     │  Lattice)  │                       │
  │     │            │  No search needed:    │
  │     │  propagate │  propagation alone     │
  │     │  alone     │  determines SAT.      │
  │     └────────────┘                       │
  │                                          │
  │     ┌────────────┐                       │
  │     │  Search    │  label() produces     │
  │     │  needed    │  LogicStream of       │
  │     │ (Unif.    │  alternatives          │
  │     │  extended) │                       │
  │     │            │  LogicT explores      │
  │     │  propagate │  fairly with bounded  │
  │     │  + label   │  depth (search_bound) │
  │     └────────────┘                       │
  └──────────────────────────────────────────┘
```

The `search_bound` parameter limits the number of labeling steps to prevent infinite loops in non-decidable theories. For decidable theories this parameter is irrelevant -- propagation always terminates.

---

## Code Examples

### Creating and Using a LogicStream

```rust
use mettail_prattail::logict::LogicStream;

// Empty stream (failure)
let empty: LogicStream<i32> = LogicStream::empty();
assert!(empty.msplit().is_none());

// Singleton stream
let single = LogicStream::unit(42);
let (val, rest) = single.msplit().expect("should have a value");
assert_eq!(val, 42);
assert!(rest.msplit().is_none());

// Stream from iterator
let stream = LogicStream::from_iter(vec![1, 2, 3]);
let results = stream.collect_all();
assert_eq!(results, vec![1, 2, 3]);
```

### Fair Interleaving

```rust
let odds  = LogicStream::from_iter(vec![1, 3, 5]);
let evens = LogicStream::from_iter(vec![2, 4, 6]);

// Unfair: all odds, then all evens
let unfair = odds.clone().mplus(evens.clone()).collect_all();
assert_eq!(unfair, vec![1, 3, 5, 2, 4, 6]);

// Fair: alternating
let fair = odds.interleave(evens).collect_all();
assert_eq!(fair, vec![1, 2, 3, 4, 5, 6]);
```

### Soft Cut (ifte)

```rust
// If test succeeds, use then-branch; otherwise, else-branch
let test = LogicStream::from_iter(vec![1, 2]);
let result = test.ifte(
    |x| LogicStream::unit(x * 10),  // then: multiply by 10
    LogicStream::unit(0),            // else: return 0
);
let results = result.collect_all();
// test succeeded: [10, 20] (both results processed)
assert!(results.contains(&10));
assert!(results.contains(&20));
```

### ConstraintTheory with TheoryAlgebra

```rust
use mettail_prattail::logict::{ConstraintTheory, TheoryAlgebra, TheoryPred};
use mettail_prattail::symbolic::BooleanAlgebra;

// Using PresburgerTheory as an example
let theory = PresburgerTheory::new(8);
let algebra = TheoryAlgebra::new(theory, 100);

// Build a predicate: x >= 3 AND x <= 7
let pred = algebra.and(
    &TheoryPred::Atom(LinearConstraint::from_gte(vec![(0, 1)], 3)),
    &TheoryPred::Atom(LinearConstraint::new(vec![(0, 1)], 7)),
);

// Satisfiability check uses propagation (no search needed)
assert!(algebra.is_satisfiable(&pred));

// Witness extraction
let witness = algebra.witness(&pred).expect("should find witness");
let val = witness.get(0);
assert!(val >= 3 && val <= 7);
```

### Negation as Finite Failure

```rust
// gnot succeeds iff the stream is empty
let empty: LogicStream<i32> = LogicStream::empty();
assert_eq!(empty.gnot().collect_all().len(), 1);  // succeeds with ()

let nonempty = LogicStream::unit(42);
assert!(nonempty.gnot().collect_all().is_empty()); // fails
```

---

## Negation Handling

Negation in the `TheoryAlgebra` bridge is subtle because `ConstraintTheory` only supports forward propagation -- there is no "negate and propagate" operation. The bridge handles negation structurally:

1. **Boolean identities.** `Not(True) = False`, `Not(False) = True`, `Not(Not(A)) = A`.

2. **De Morgan push-down.** `Not(And(A, B)) = Or(Not(A), Not(B))` and `Not(Or(A, B)) = And(Not(A), Not(B))`.

3. **Atomic negation.** `Not(Atom(c))` cannot be propagated through the theory. The store is returned unchanged, and the negation is tracked structurally in the `TheoryPred`. At witness validation time, `evaluate(Not(Atom(c)), witness)` checks that the witness does *not* satisfy `c`.

This means `TheoryAlgebra` uses negation-as-failure (NAF) semantics for atomic negation, while `PresburgerAlgebra` (direct path) uses classical negation via NFA complement. The two may diverge on predicates involving atomic negation; cross-validation tests document the expected behavior.

---

## Performance Characteristics

| Operation | Complexity | Notes |
|-----------|-----------|-------|
| `msplit` | O(1) amortized | Deque pop from front |
| `mplus` | O(\|b\|) | Extend deque with all branches of `b` |
| `interleave` | O(\|a\| + \|b\|) | Merge two deques element-by-element |
| `fair_conjoin(f)` | O(\|stream\| * \|f(x)\|) | Applies `f` to each, interleaves |
| `collect_bounded(n)` | O(n * msplit_cost) | At most `n` calls to `msplit` |
| `ifte` | O(msplit_cost + then/else) | One `msplit` for the test |
| `once` | O(msplit_cost) | One `msplit`, discard rest |
| `gnot` | O(msplit_cost) | One `msplit` to check emptiness |

Memory: each `Branch::Suspended` allocates one boxed closure (~16-24 bytes + captured state). The `VecDeque` grows dynamically. For bounded searches (`collect_bounded`), memory is proportional to the search bound times the average closure size.

---

## Citation

- Kiselyov, O., Shan, C., Friedman, D. P. & Sabry, A. (2005). "Backtracking, Interleaving, and Terminating Monad Transformers." *ICFP 2005*. ACM, pp. 192--203. DOI: [10.1145/1086365.1086390](https://doi.org/10.1145/1086365.1086390)
- Hemann, J. & Friedman, D. P. (2013). "muKanren: A Minimal Functional Core for Relational Programming." *Scheme Workshop 2013*.
