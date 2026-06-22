# LogicT Fair Backtracking Search Framework

**Status:** Core infrastructure — always compiled (`pub mod logict;` in `prattail/src/lib.rs`; no Cargo feature gate)
**Module:** `prattail/src/logict.rs`
**Benchmark target:** `bench_logict` (`prattail/benches/bench_logict.rs`)
**Dependencies:** `std` only (`VecDeque`, `HashMap`, `HashSet`); bridges to `crate::symbolic::BooleanAlgebra`

> **This is the deep engine reference.** It is the full API, algorithm, and
> mathematical account of the LogicT logic-monad, the `ConstraintTheory` trait,
> the `TheoryAlgebra` bridge, quantified-formula evaluation, theory combination,
> and associative-commutative (AC) matching. For the *integration narrative* —
> how this engine sits under the symbolic-predicate substrate, plus the four
> rendered figures (fair-search swimlane, theory-algebra bridge, quantified-eval
> sequence, theory-combination) — read the companion document
> [13 — The Constraint-Theory Engine: LogicT Under the Substrate](../../../../docs/architecture/symbolic-predicates/13-constraint-theory-engine.md).
> That page links back here for depth; this page links there for figures and the
> substrate wiring rather than duplicating them.
>
> The mechanized proofs that ground §9 (theory combination) live in
> [`TheoryCombination.v`](../../../../formal/rocq/symbolic_algebra/theories/TheoryCombination.v)
> and are surveyed in
> [10 — Formal Verification and Tests](../../../../docs/architecture/symbolic-predicates/10-formal-verification-and-tests.md).
> The bounded-search diagnostic is
> [`LT01`](../../diagnostics/logict/LT01.md) (`logict-search-bound-exceeded`).

---

## Table of contents

1. [Header and gating](#1-header-and-gating)
2. [Intuition: why fair search matters](#2-intuition-why-fair-search-matters)
3. [Theory: the logic monad and `msplit`](#3-theory-the-logic-monad-and-msplit)
4. [The operation set](#4-the-operation-set)
5. [Representation: `VecDeque`, `Branch`, `BranchResult`](#5-representation-vecdeque-branch-branchresult)
6. [The `ConstraintTheory` trait](#6-the-constrainttheory-trait)
7. [The `TheoryAlgebra` bridge](#7-the-theoryalgebra-bridge)
8. [Quantified evaluation](#8-quantified-evaluation)
9. [Theory combination](#9-theory-combination)
10. [AC-matching: multiset partitions](#10-ac-matching-multiset-partitions)
11. [Integration with the substrate](#11-integration-with-the-substrate)
12. [Performance characteristics](#12-performance-characteristics)
13. [Diagnostics](#13-diagnostics)
14. [References](#14-references)

A note on notation before we begin: throughout this document, `⊤` denotes
logical truth, `⊥` logical falsity, `¬` negation, `∧` conjunction, `∨`
disjunction, `⇒` implication, `∀` universal quantification, `∃` existential
quantification, and `∈` set membership. The fair-bind operator of the logic
monad is written `≫-` (read "fair bind", the LogicT analogue of the monadic
`>>=`). All mathematical expressions are quoted in backticks per the
documentation guidelines.

---

## 1. Header and gating

`logict` is **core infrastructure**, not an optional feature. The module is
declared unconditionally:

```rust
// prattail/src/lib.rs:393
pub mod logict;
```

There is no `#[cfg(feature = "logict")]` anywhere in `prattail/src`, and
`logict` does not appear in the `[features]` table of `prattail/Cargo.toml`. It
is always compiled because the symbolic-predicate guard machinery (quantified
evaluation, theory algebras) depends on it directly. A dedicated criterion
benchmark target named `bench_logict` exercises the hot paths; the *name*
`logict` therefore appears in `Cargo.toml` only as a `[[bench]]` entry, which is
distinct from a build feature.

The module's public surface, all exported from `prattail::logict`, falls into
five groups:

| Group | Public items |
|---|---|
| Search stream | `LogicStream<T>`, `LogicStreamIter<T>` |
| Constraint domain | `ConstraintTheory` (trait) |
| Boolean-algebra bridge | `TheoryAlgebra<T>`, `TheoryPred<T>` |
| Quantified FOL | `QuantifiedFormula`, `QuantifiedDomain`, `QuantifiedArg`, `evaluate_quantified`, `evaluate_quantified_with_theory`, `TriState` |
| AC-matching | `MultisetPartition<T>`, `multiset_partitions`, `multiset_select` |

The internal types `Branch<T>` and `BranchResult<T>` are private (they back
`LogicStream`'s representation, §5) and are documented here for completeness,
not for use.

---

## 2. Intuition: why fair search matters

Consider a naïve depth-first backtracking search that explores constraint
alternatives:

```text
                    root
                  ╱      ╲
              left        right
             ╱  │  ╲         │
           l1  l2  l3       r1
          ╱  ╲
        ...   (infinite)
```

Depth-first search commits to the `left` branch and descends into `l1`, then
`l1`'s children, then their children, potentially forever. If the left subtree
is infinite (or just very deep), the `right` branch is *starved* — `r1` is never
explored, even though it might be the witness we need.

This starvation is not hypothetical. In constraint propagation over unbalanced
domains — say a `PresburgerTheory` searching over integer assignments, or a
`UnificationTheory` exploring alternative constructors — the search tree can be
highly asymmetric. The constraint `x + y ≤ 100 ∧ x ≥ 0 ∧ y ≥ 0` has `5151`
solutions; naïve depth-first search by `x` would enumerate all `101` values of
`x` (and for each, all valid `y`) before considering any alternative
decomposition.

LogicT solves this with **fair disjunction**: the `interleave` operation
alternates between branches, guaranteeing that both sides of any disjunction are
explored infinitely often. No branch can be starved, regardless of tree shape.
This is precisely why a *bounded* search budget (`collect_bounded`) can return a
witness where naïve depth-first would diverge: the budget is spent
breadth-first across the round-robin frontier, so a shallow witness in a "late"
branch is found within the budget instead of being trapped behind an infinite
"early" branch.

---

## 3. Theory: the logic monad and `msplit`

LogicT is the Rust realization of the backtracking **logic monad** of Kiselyov,
Shan, Friedman & Sabry (ICFP 2005). The central insight of that paper is that a
single primitive, `msplit`, is expressive enough to *derive* every other search
combinator — fair disjunction, fair conjunction, soft cut, hard cut, and
negation-as-failure — while remaining implementable without unbounded native
stack growth.

### 3.1 Constructors versus derived operations

We distinguish the monad's *generators* (how answers enter a stream) from its
*derived operations* (how streams are recombined). The classical
`MonadPlus`/`LogicT` vocabulary and this crate's names line up as follows:

| Monad concept | Meaning | This crate |
|---|---|---|
| `mzero` | the empty answer set (failure); identity of `mplus` | `LogicStream::empty()` |
| `return v` / `unit v` | the singleton answer `v` | `LogicStream::unit(v)` |
| `mplus` | answer-set union, biased/unfair | `LogicStream::mplus` |
| `msplit` | the *primitive*: split a stream into `(first, rest)` | `LogicStream::msplit` |
| `interleave` | fair answer-set union | `LogicStream::interleave` |
| `≫-` (fair bind) | fair monadic bind | `LogicStream::fair_conjoin` |
| `ifte` | soft cut (committed-choice if-then-else) | `LogicStream::ifte` |
| `once` | hard cut (commit to first answer) | `LogicStream::once` |
| `lnot` / negation-as-failure | succeed iff the stream is empty | `LogicStream::gnot` |

`empty`, `unit`, `from_iter`, and `suspend` are *constructors*: they introduce
answers (or a suspended producer of answers) into a `LogicStream`. `msplit` is
the sole *eliminator* primitive. `mplus`, `interleave`, `fair_conjoin`, `ifte`,
`once`, and `gnot` are *derived* — each is implementable purely in terms of
`msplit` plus the constructors, and this crate implements them that way.

### 3.2 The `msplit` primitive

`msplit` deconstructs a search stream into its first answer and the remainder:

```text
msplit : LogicStream<T> → Option<(T, LogicStream<T>)>
```

- If the stream has answers, it returns `Some((first, rest))`.
- If the stream is exhausted, it returns `None`.

This is analogous to pattern-matching a list as `head ∷ tail`, but for a
potentially lazy, branching computation. Crucially, `msplit` *forces just enough*
of the stream to expose one answer: suspended branches are evaluated on demand,
and any branches they spawn are re-queued (§5) rather than recursed into.

### 3.3 Monad laws

`LogicStream` with `unit` and `fair_conjoin` forms a monad. Writing `m ≫- f`
for `m.fair_conjoin(f)`, the three monad laws hold *as answer multisets* (order
may differ because `fair_conjoin` interleaves):

```text
(L1) left identity   unit(a) ≫- f          ≡  f(a)
(L2) right identity  m ≫- unit             ≡  m
(L3) associativity   (m ≫- f) ≫- g         ≡  m ≫- (λx. f(x) ≫- g)
```

`empty` and `interleave` additionally satisfy the `MonadPlus`-style identities,
again up to answer-multiset equality:

```text
(P1) left zero       empty ≫- f            ≡  empty
(P2) identity        interleave(empty, m)  ≡  m   ≡  interleave(m, empty)
(P3) commutativity*  interleave(a, b)      ≈  interleave(b, a)
```

`(P3)` is marked with `*` because `interleave` is commutative on the *set* of
answers produced but not on their *order* (it is a round-robin merge, so the
first answer comes from the left operand). The crate's tests
`interleave_alternates_results`, `fair_conjoin_does_not_starve`,
`mplus_concatenates_streams`, and `interleave_with_empty` pin down these
behaviors concretely.

### 3.4 The fairness theorem

**Theorem (Fairness of `interleave`).** For any two `LogicStream`s `a` and `b`,
every answer of `a` and every answer of `b` appears in `interleave(a, b)` within
a finite prefix. Formally: if `a` has an `i`-th answer `aᵢ` and `b` has a `j`-th
answer `bⱼ`, then both appear among the first `2·max(i, j)` answers of
`interleave(a, b)`.

*Proof sketch.* The implementation (§5) builds the merged queue by alternately
pushing one branch from `a`, then one branch from `b`, until one side is
exhausted, then appending the rest of the other side. After `2n` pushes, at
least `n` branches from each non-exhausted source have been enqueued ahead of
position `2n`. Because `msplit` consumes the queue strictly from the front (FIFO)
and only ever appends spawned branches to the back, an answer enqueued at
position `p` is produced after at most `p` front-pops. Hence `aᵢ` and `bⱼ`
surface within a bounded prefix; neither source can be starved by the other. ∎

`fair_conjoin` (`≫-`) lifts this guarantee to monadic bind: applying `f` to each
answer and then *interleaving* every resulting sub-stream means that no single
`f(aₖ)` — however prolific or infinite — can starve the answers of `f(aₘ)` for
`m ≠ k`.

---

## 4. The operation set

### 4.1 Operation table (verified against `logict.rs`)

Every operation below is a method on `LogicStream<T>` (with `T: Send + 'static`)
unless marked as a constructor. Signatures are stated with the real Rust types.

| Operation | Signature | Fairness | Semantics |
|---|---|---|---|
| `empty()` *(ctor)* | `() → LogicStream<T>` | — | `mzero`: empty stream / failure. Identity of `mplus` and `interleave`. |
| `unit(v)` *(ctor)* | `T → LogicStream<T>` | — | Singleton stream containing `v`. |
| `from_iter(it)` *(ctor)* | `IntoIterator<Item = T> → LogicStream<T>` | — | One `Ready` branch per item, in iterator order. |
| `suspend(f)` *(ctor)* | `(FnOnce() → LogicStream<T>) → LogicStream<T>` | — | Defer a whole sub-stream; forced lazily by `msplit`. Always emits a `Fork` (§5). |
| `msplit()` | `LogicStream<T> → Option<(T, LogicStream<T>)>` | — | **The primitive.** First answer + remainder, or `None`. |
| `mplus(other)` | `LogicStream<T> → LogicStream<T>` | **unfair** | Concatenation: all of `self`, then all of `other`. |
| `interleave(other)` | `LogicStream<T> → LogicStream<T>` | **fair** | Round-robin merge of `self` and `other`. |
| `fair_conjoin(f)` | `(T → LogicStream<U>) → LogicStream<U>` | **fair** | `≫-`: map each answer to a sub-stream, interleave all results. |
| `ifte(then, else)` | `(T → LogicStream<U>, LogicStream<U>) → LogicStream<U>` | fair within `then` | Soft cut: if `self` yields ≥ 1 answer, apply `then` to each; else use `else`. |
| `once()` | `LogicStream<T> → LogicStream<T>` | — | Hard cut: keep only the first answer. |
| `gnot()` | `LogicStream<T> → LogicStream<()>` | — | Negation as finite failure: `unit(())` iff `self` is empty, else `empty()`. |
| `map(f)` | `(T → U) → LogicStream<U>` | eager | Eagerly collect, then map (preserves all answers). |
| `filter(p)` | `(&T → bool) → LogicStream<T>` | eager | Eagerly collect, then retain answers satisfying `p`. |
| `collect_bounded(n)` | `usize → Vec<T>` | — | Up to `n` answers via repeated `msplit`. Terminates on infinite streams. |
| `collect_all()` | `() → Vec<T>` | — | **All** answers. **Diverges on an infinite stream** — see the warning below. |
| `is_empty()` | `() → bool` | — | `true` iff `msplit()` is `None` (consumes the stream). |
| `count_bounded(n)` | `usize → usize` | — | `collect_bounded(n).len()`. |
| `into_iter()` | `LogicStream<T> → LogicStreamIter<T>` | lazy | Lazy `Iterator`: each `next()` performs one `msplit`. |

> **Divergence warning.** `collect_all` and the `map`/`filter` helpers (which
> call `collect_all` internally) loop until the stream is exhausted. On an
> infinite or unbounded stream they do not terminate. For any stream whose size
> is not known to be finite — in particular the output of `multiset_partitions`
> over a large bag, or a `ConstraintTheory::label` that enumerates a
> semi-decidable domain — use `collect_bounded(limit)` or the lazy
> `into_iter()` adapter instead. The bounded variants are the resource meter
> that the `LT01` diagnostic (§13) reports on.

### 4.2 Pre/post-conditions for the load-bearing operations

**`msplit`**

```text
Pre:   self is a valid LogicStream (finitely or infinitely branching).
Post:  if self has ≥ 1 answer, returns Some((first, rest)) where
          • first is the earliest available answer (front of the queue), and
          • rest is a valid LogicStream containing exactly the remaining answers;
       if self is exhausted, returns None.
Effect: forces suspended branches at the front until an answer is exposed or the
        queue empties; spawned branches are appended to the back (never recursed).
```

**`interleave`**

```text
Pre:   self, other are valid LogicStreams.
Post:  result is a LogicStream such that
          ∀ i. (self has an i-th answer aᵢ)  ⇒ aᵢ ∈ result, and
          ∀ j. (other has a j-th answer bⱼ)  ⇒ bⱼ ∈ result,
       with the fairness bound of §3.4 (neither source is starved).
```

**`fair_conjoin` (`≫-`)**

```text
Pre:   self : LogicStream<T>,  f : T → LogicStream<U>.
Post:  result ≡ fold(self.map(f), empty, interleave)  (up to answer order);
       i.e. f is applied to every answer of self and all resulting sub-streams
       are interleaved, so no single f(answer) can starve the others.
```

### 4.3 Literate algorithms

The three derived operations whose behavior is most subtle are presented below
as Knuth-style literate chunks. Line numbers cite `prattail/src/logict.rs`.

**Algorithm `Msplit` — the eliminator primitive** *(logict.rs:157–183)*

```text
⟨Msplit(self) → Option<(T, LogicStream<T>)>⟩ ≡
  1.  while the branch queue is non-empty:
  2.      branch ← pop_front(queue)
  3.      case branch of
  4.        Ready(v):                       ▷ an answer is immediately available
  5.            return Some((v, self))      ▷ self now holds the untouched remainder
  6.        Suspended(thunk):               ▷ force exactly this suspended producer
  7.            case thunk() of
  8.              Yield(v, more):           ▷ answer plus extra branches (reserved, §5)
  9.                  push_back(queue, b) for each b in more
 10.                  return Some((v, self))
 11.              Fail:                      ▷ this branch produced nothing
 12.                  continue               ▷ skip; try the next branch
 13.              Fork(more):                ▷ a suspended sub-stream unfolds here
 14.                  push_back(queue, b) for each b in more
 15.                  continue               ▷ no answer yet; keep draining
 16.  return None                            ▷ queue drained without an answer
```

The discipline that makes `Msplit` fair is on lines 9 and 14: spawned branches
go to the **back** of the FIFO queue, so older branches are always served first
(round-robin), and a freshly-unfolded infinite sub-stream cannot jump the queue.

**Algorithm `Interleave` — fair disjunction** *(logict.rs:205–231)*

```text
⟨Interleave(self, other) → LogicStream<T>⟩ ≡
  1.  result ← empty queue with capacity |self| + |other|
  2.  iₐ ← iterator over self's branches;  i_b ← iterator over other's branches
  3.  loop:
  4.      case (next(iₐ), next(i_b)) of
  5.        (Some a, Some b):  push_back(result, a); push_back(result, b)   ▷ alternate
  6.        (Some a, None):    push_back(result, a); extend(result, iₐ); break ▷ self outlasts
  7.        (None, Some b):    push_back(result, b); extend(result, i_b); break ▷ other outlasts
  8.        (None, None):      break                                         ▷ both done
  9.  return LogicStream { branches: result }
```

`Interleave` is *eager in the branch list but lazy in the answers*: it splices
the two branch queues in `a, b, a, b, …` order without forcing any `Suspended`
thunk. The thunks are forced later, on demand, by `Msplit`. This is the source
of the `O(|a| + |b|)` cost in §12.

**Algorithm `FairConjoin` — fair bind (`≫-`)** *(logict.rs:240–279)*

```text
⟨FairConjoin(self, f) → LogicStream<U>⟩ ≡
  1.  accumulated ← empty()
  2.  for each branch in self's branches:
  3.      case branch of
  4.        Ready(v):                       ▷ immediate answer → its sub-search
  5.            sub ← f(v)
  6.        Suspended(thunk):               ▷ force, then apply f to each surfaced answer
  7.            case thunk() of
  8.              Yield(v, more):  sub ← f(v); for Ready(v′) in more: sub ← interleave(sub, f(v′))
  9.              Fail:            sub ← empty()
 10.              Fork(more):      sub ← empty(); for Ready(v′) in more: sub ← interleave(sub, f(v′))
 11.        accumulated ← interleave(accumulated, sub)   ▷ fold-by-interleave
 12.  return accumulated
```

Line 11 is the heart of fairness: every sub-stream `f(v)` is folded into the
result with `interleave`, never concatenated, so the answers of all sub-searches
are produced round-robin (the test `fair_conjoin_does_not_starve` asserts the
`[11, 21, 12, 22]` interleaved order rather than the depth-first
`[11, 12, 21, 22]`).

---

## 5. Representation: `VecDeque`, `Branch`, `BranchResult`

### 5.1 Why an explicit queue rather than CPS

PraTTaIL implements `LogicStream<T>` as an explicit `VecDeque<Branch<T>>`, *not*
as the success/failure continuation-passing (SFKT) representation of the original
paper. The reasons:

1. **Stack safety.** CPS-based LogicT can overflow the native stack on deep
   searches. The explicit queue keeps all search state on the heap, consistent
   with PraTTaIL's trampoline parser (which likewise replaces recursion with an
   explicit stack).

2. **Debuggability.** The `VecDeque` is inspectable: `LogicStream`'s `Debug`
   impl reports the live branch count (`"LogicStream(N branches)"`). Nested CPS
   closures are opaque.

3. **Memory efficiency.** Suspension uses one `Box<dyn FnOnce() -> BranchResult<T>>`
   per suspended branch, but the queue itself is a flat `VecDeque` with `O(1)`
   amortized push/pop. There is no chain of nested closures to walk.

4. **Architectural consistency.** The same explicit-stack philosophy powers the
   trampoline parser, so the codebase is uniform in how it eliminates recursion.

### 5.2 `Branch` and `BranchResult`

```rust
/// A branch in the search tree.
enum Branch<T> {
    /// A value ready to yield.
    Ready(T),
    /// A suspended computation returning zero or more results.
    Suspended(Box<dyn FnOnce() -> BranchResult<T> + Send>),
}

/// Result of evaluating a branch.
#[allow(dead_code)]
enum BranchResult<T> {
    /// Yield a value, with additional branches to explore.
    Yield(T, Vec<Branch<T>>),
    /// No result from this branch.
    Fail,
    /// Fork into sub-branches (no immediate result).
    Fork(Vec<Branch<T>>),
}
```

`LogicStream<T>` itself is simply:

```rust
pub struct LogicStream<T> {
    /// Branch queue for round-robin fair scheduling.
    branches: VecDeque<Branch<T>>,
}
```

### 5.3 The reserved variants — `Yield` and `Fail` are not live

`BranchResult` is part of the documented LogicT `msplit` protocol, and `Msplit`
and `FairConjoin` both contain exhaustive match arms for all three variants. In
the *current* code, however, the only constructor that produces a `BranchResult`
is `LogicStream::suspend`, and it always returns `Fork(...)`:

```rust
// logict.rs:132–139 — suspend always emits Fork
pub fn suspend(f: impl FnOnce() -> LogicStream<T> + Send + 'static) -> Self {
    let mut branches = VecDeque::with_capacity(1);
    branches.push_back(Branch::Suspended(Box::new(move || {
        let stream = f();
        Fork(stream.branches.into_iter().collect())   // ← never Yield, never Fail
    })));
    LogicStream { branches }
}
```

Consequently `BranchResult::Yield` and `BranchResult::Fail` are **reserved, not
live**: no present code path constructs them, which is why the enum carries
`#[allow(dead_code)]`. They are retained for two reasons: (a) they document the
full `msplit` protocol from Kiselyov §3.2, and (b) they keep the door open for a
future constructor that produces an answer directly from a suspension
(`Yield`) or prunes a branch in place (`Fail`) without re-allocating a
`LogicStream`. A reader should *not* infer that an answer can currently arrive
via `Yield` or that a branch can fail via `Fail`; today, answers arrive only via
`Ready`, and pruning happens only by a `Fork` that contributes no `Ready`
branch.

### 5.4 The scheduling invariant

`Msplit` pops from the **front** and pushes spawned branches to the **back**.
That single FIFO discipline is what realizes the fairness theorem of §3.4: an
"older" branch is always nearer the front than the branches it spawns, so no
branch — not even one that unfolds an infinite sub-stream — can monopolize the
search.

---

## 6. The `ConstraintTheory` trait

`ConstraintTheory` is the abstraction that lets *any* constraint domain plug into
PraTTaIL's symbolic-automata framework. It separates two orthogonal concerns:

1. **Propagation** — deterministic constraint narrowing. Adding a constraint to
   the store may detect inconsistency (return `None`) or yield a refined store.
   For *decidable* theories, propagation alone decides satisfiability.

2. **Labeling** — non-deterministic search choices. For theories that need
   search (e.g. choosing among alternative constructor matches), `label`
   produces a `LogicStream` of constraint alternatives that LogicT explores
   fairly. A decidable theory returns `LogicStream::empty()`.

### 6.1 Specification (verbatim trait, with pre/post-conditions)

```rust
pub trait ConstraintTheory: Clone + fmt::Debug + Send + Sync + 'static {
    type Constraint: Clone + fmt::Debug + Eq + Hash + Send + Sync + 'static;
    type Assignment: Clone + fmt::Debug + Send + Sync + 'static;
    type Store: Clone + fmt::Debug + Send + Sync + 'static;

    /// Create an empty (unconstrained) store.
    /// Post: result is consistent and admits every assignment in the domain.
    fn empty_store(&self) -> Self::Store;

    /// Add a constraint and propagate.
    /// Pre:  is_consistent(store).
    /// Post: if Some(s′), then s′ is consistent and, for every assignment a,
    ///         (evaluate(c, a) ∧ a ⊨ store)  ⇔  a ⊨ s′;
    ///       if None, then store ∧ c is unsatisfiable.
    fn propagate(&self, store: &Self::Store, c: &Self::Constraint) -> Option<Self::Store>;

    /// Check consistency without adding a constraint.
    /// Post: result ⇔ (∃ assignment a. a ⊨ store).
    fn is_consistent(&self, store: &Self::Store) -> bool;

    /// Extract a witness from a consistent store.
    /// Pre:  is_consistent(store).
    /// Post: if Some(a), then a ⊨ store; if None, the store needs labeling
    ///       (or is inconsistent).
    fn witness(&self, store: &Self::Store) -> Option<Self::Assignment>;

    /// Enumerate labeling choices for search.
    /// Pre:  is_consistent(store).
    /// Post: a LogicStream of constraints that, added via propagate, enumerate
    ///       all valid extensions of the store. Decidable theories: empty().
    fn label(&self, store: &Self::Store) -> LogicStream<Self::Constraint>;

    /// Decide whether an assignment satisfies a constraint.
    /// Post: result ⇔ (a ⊨ c).
    fn evaluate(&self, c: &Self::Constraint, a: &Self::Assignment) -> bool;
}
```

The three associated types carry the theory's vocabulary: `Constraint` is the
guard-predicate language, `Assignment` is the concrete witness (a domain
element), and `Store` is accumulated constraint state. The trait bounds
(`Clone + Debug + Send + Sync + 'static`, plus `Eq + Hash` on `Constraint`) are
exactly what the bridge needs to put constraints in hash sets and move stores
across the fair-search frontier.

### 6.2 `label` behavior per theory type

| Theory | Decidability | `label()` behavior | Rationale |
|---|---|---|---|
| `PresburgerTheory` | Decidable | `LogicStream::empty()` | NFA emptiness decides satisfiability; no search choices. |
| `LatticeTheory` | Decidable | `LogicStream::empty()` | Finite universe; transitive-closure decides all relationships. |
| `UnificationTheory` | Decidable (core) | `empty()` for core; alternatives for extended custom-match | Martelli–Montanari unification is deterministic; extended pattern matching may branch. |
| User-defined | Varies | Domain-specific stream | Implement `ConstraintTheory`; obtain `BooleanAlgebra` for free via `TheoryAlgebra`. |

The decidable theories make the `search_bound` of §7 irrelevant: with an empty
`label`, no labeling step is ever taken and propagation always terminates. The
bound only bites when a theory's `label` is non-empty (the `LT01` case, §13).

### 6.3 A complete, in-tree example: `PropTheory`

The crate's own test module defines a minimal propositional theory that
implements the entire trait. It is reproduced here because it is *guaranteed to
compile and behave as shown* (it is exercised by the unit tests
`constraint_theory_consistent_store`, `constraint_theory_contradiction`, and
`constraint_theory_evaluate`):

```rust
/// Constraints are propositional atoms, asserted or negated.
/// The store is the set of asserted and negated atoms.
/// Satisfiable iff no atom is both asserted and negated.
#[derive(Clone, Debug)]
struct PropTheory;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum PropConstraint { Assert(String), Negate(String) }

#[derive(Clone, Debug)]
struct PropAssignment(std::collections::HashMap<String, bool>);

#[derive(Clone, Debug)]
struct PropStore {
    asserted: std::collections::HashSet<String>,
    negated:  std::collections::HashSet<String>,
}

impl ConstraintTheory for PropTheory {
    type Constraint = PropConstraint;
    type Assignment = PropAssignment;
    type Store      = PropStore;

    fn empty_store(&self) -> PropStore {
        PropStore {
            asserted: std::collections::HashSet::new(),
            negated:  std::collections::HashSet::new(),
        }
    }

    fn propagate(&self, store: &PropStore, c: &PropConstraint) -> Option<PropStore> {
        let mut new_store = store.clone();
        match c {
            PropConstraint::Assert(name) => {
                if new_store.negated.contains(name) { return None; } // ⊥: a ∧ ¬a
                new_store.asserted.insert(name.clone());
            },
            PropConstraint::Negate(name) => {
                if new_store.asserted.contains(name) { return None; } // ⊥
                new_store.negated.insert(name.clone());
            },
        }
        Some(new_store)
    }

    fn is_consistent(&self, store: &PropStore) -> bool {
        store.asserted.intersection(&store.negated).next().is_none()
    }

    fn witness(&self, store: &PropStore) -> Option<PropAssignment> {
        if !self.is_consistent(store) { return None; }
        let mut a = std::collections::HashMap::new();
        for name in &store.asserted { a.insert(name.clone(), true); }
        for name in &store.negated  { a.insert(name.clone(), false); }
        Some(PropAssignment(a))
    }

    fn label(&self, _store: &PropStore) -> LogicStream<PropConstraint> {
        LogicStream::empty() // decidable: propagation alone decides
    }

    fn evaluate(&self, c: &PropConstraint, a: &PropAssignment) -> bool {
        match c {
            PropConstraint::Assert(name) =>  *a.0.get(name).unwrap_or(&false),
            PropConstraint::Negate(name) => !*a.0.get(name).unwrap_or(&false),
        }
    }
}
```

`PropTheory` is decidable, so its `label` is empty; the entire satisfiability
decision rides on `propagate` detecting the `a ∧ ¬a` contradiction. This is the
canonical shape of a decidable `ConstraintTheory`.

---

## 7. The `TheoryAlgebra` bridge

`TheoryAlgebra<T>` wraps any `ConstraintTheory` and provides a `BooleanAlgebra`
implementation, so a domain solver integrates with
`SymbolicAutomaton<TheoryAlgebra<T>>` — and thereby with minterm computation,
determinization, and the lint analyses — without touching the automata.

```rust
#[derive(Clone, Debug)]
pub struct TheoryAlgebra<T: ConstraintTheory> {
    pub theory: T,
    /// Maximum number of labeling/answer steps drawn from the fair search.
    pub search_bound: usize,
}
```

### 7.1 `TheoryPred<T>` — Boolean combinations of constraints

The bridge's `Predicate` type is a standard Boolean AST over theory atoms:

```text
TheoryPred<T> ::= True
               |  False
               |  Atom(T::Constraint)
               |  And(TheoryPred<T>, TheoryPred<T>)
               |  Or (TheoryPred<T>, TheoryPred<T>)
               |  Not(TheoryPred<T>)
```

Wrapping atoms in this AST means the bridge handles arbitrary `∧`/`∨`/`¬`
combinations even when the underlying theory supports only forward propagation
(no native negation or disjunction). `TheoryPred<T>` implements `PartialEq`,
`Eq`, and `Hash` *structurally* (so it can serve as the automaton's predicate
alphabet), delegating to `T::Constraint`'s own `Eq`/`Hash`.

### 7.2 `collect_constraints` — folding a `TheoryPred` into a store stream

The bridge's private workhorse turns a `TheoryPred` into a `LogicStream` of
satisfying stores, using the fair operators of §4 for the connectives.

**Algorithm `CollectConstraints`** *(logict.rs:1240–1314)*

```text
⟨CollectConstraints(self, pred, store) → LogicStream<Store>⟩ ≡
  1.  case pred of
  2.    True:        return unit(store)                       ▷ ⊤ admits the store unchanged
  3.    False:       return empty()                           ▷ ⊥ admits nothing
  4.    Atom(c):     case theory.propagate(store, c) of       ▷ narrow by the atom
  5.                   Some(s′): return unit(s′)
  6.                   None:     return empty()                ▷ atom contradicts the store
  7.    And(a, b):   aₛ ← CollectConstraints(a, store)         ▷ conjunction = fair bind
  8.                 return aₛ.fair_conjoin(λ s. CollectConstraints(b, s))
  9.    Or(a, b):    aₛ ← CollectConstraints(a, store)         ▷ disjunction = fair merge
 10.                 bₛ ← CollectConstraints(b, store)
 11.                 return interleave(aₛ, bₛ)
 12.    Not(inner):  case inner of                             ▷ De Morgan push-down
 13.                   True:        return empty()             ▷ ¬⊤ = ⊥
 14.                   False:       return unit(store)         ▷ ¬⊥ = ⊤
 15.                   Not(inner₂): return CollectConstraints(inner₂, store)  ▷ ¬¬A = A
 16.                   And(a, b):   return interleave(¬a-stores, ¬b-stores)   ▷ ¬(A∧B)=¬A∨¬B
 17.                   Or(a, b):    return (¬a-stores).fair_conjoin(λ s. ¬b-stores) ▷ ¬(A∨B)=¬A∧¬B
 18.                   Atom(_):     return unit(store)         ▷ atomic NAF — tracked, validated later
```

Two subtleties deserve emphasis:

- **Conjunction is `fair_conjoin`** (line 8): each store produced by `a` becomes
  the input store for `b`, and all the resulting `b`-searches are interleaved.
  This threads the constraint state through the conjunction *and* keeps the
  search fair.
- **Atomic negation is negation-as-failure** (line 18): `propagate` cannot add a
  *negated* atom (the theory only narrows by positive constraints), so
  `¬Atom(c)` leaves the store unchanged and defers the check. The negation is
  carried structurally in the `TheoryPred` and enforced at witness time by
  `evaluate(¬Atom(c), witness)` — i.e. the witness must *not* satisfy `c`.

### 7.3 `witness` and `is_satisfiable`

`is_satisfiable(pred)` is defined as `witness(pred).is_some()`. The `witness`
method runs the store stream, takes a bounded prefix, and validates each
candidate against the *full* predicate (so structurally-tracked atomic negations
are honored):

**Algorithm `Witness`** *(logict.rs:1370–1396)*

```text
⟨Witness(self, pred) → Option<Assignment>⟩ ≡
  1.  store  ← theory.empty_store()
  2.  stores ← CollectConstraints(pred, store).collect_bounded(search_bound)
  3.  for each s in stores:
  4.      if theory.witness(s) = Some(w) and self.evaluate(pred, w):   ▷ direct witness
  5.          return Some(w)
  6.      ▷ otherwise try labeling this store (non-decidable theories)
  7.      for each label in theory.label(s).collect_bounded(search_bound):
  8.          if theory.propagate(s, label) = Some(s′)
  9.             and theory.witness(s′) = Some(w)
 10.             and self.evaluate(pred, w):
 11.              return Some(w)
 12.  return None                                                       ▷ no witness within budget
```

Line 2's `collect_bounded(search_bound)` is the *first* resource gate (it caps
how many satisfying stores are drawn from the fair search), and line 7's bound is
the *second* (it caps labeling alternatives per store). For a decidable theory,
`label` is empty, so lines 7–11 are vacuous and the decision is made entirely by
propagation plus the line-4 witness check. The `evaluate` re-check on lines 4 and
10 is what makes atomic negation-as-failure sound: a store that was admitted only
because a `¬Atom` was left unpropagated is rejected here unless the produced witness truly
falsifies the negated atom.

### 7.4 `BooleanAlgebra` smart constructors

`TheoryAlgebra`'s `and`/`or`/`not` perform the obvious `⊤`/`⊥` simplifications
(e.g. `and(⊤, b) = b`, `or(a, ⊤) = ⊤`, `not(not(a)) = a`) before constructing a
node, keeping predicates small. `true_pred`/`false_pred` return `TheoryPred::True`/
`TheoryPred::False`, and `evaluate` recurses structurally, bottoming out at
`theory.evaluate` for atoms. These are exercised by the
`theory_algebra_tests` module (`theory_algebra_disjunction_satisfiable`,
`theory_algebra_contradiction_unsatisfiable`, `theory_algebra_negation`, etc.).

### 7.5 Negation: bridge NAF versus a direct algebra

Because the bridge uses **negation-as-failure** for atomic negation while a
direct decision-procedure algebra (e.g. `PresburgerAlgebra`, which complements
NFAs) uses **classical** negation, the two paths can diverge on predicates that
negate atoms. This is intended: the bridge is the *general* path that works for
any theory, and the direct algebra is a *faster, theory-specific* path where the
theory happens to support exact complementation. Cross-validation tests document
the agreed behavior. The mirror of this distinction at the substrate level — and
why "don't know" is collapsed to *rejection* rather than admission — is described
in [13 §5](../../../../docs/architecture/symbolic-predicates/13-constraint-theory-engine.md).

### 7.6 A complete `TheoryAlgebra` example (in-tree, decidable)

This example uses `PropTheory` from §6.3 and is exactly the
`theory_algebra_disjunction_satisfiable` test, so it is guaranteed valid:

```rust
use mettail_prattail::logict::{TheoryAlgebra, TheoryPred};
use mettail_prattail::symbolic::BooleanAlgebra;
// PropTheory / PropConstraint as defined in §6.3.

let algebra = TheoryAlgebra::new(PropTheory, 100);

// (x ∧ ¬x) ∨ y — the left disjunct is ⊥, the right is satisfiable.
let pred = algebra.or(
    &algebra.and(
        &TheoryPred::Atom(PropConstraint::Assert("x".into())),
        &TheoryPred::Atom(PropConstraint::Negate("x".into())),
    ),
    &TheoryPred::Atom(PropConstraint::Assert("y".into())),
);

assert!(algebra.is_satisfiable(&pred));      // the `y` disjunct yields a witness
```

For a *decidable arithmetic* theory the same shape applies with
`PresburgerTheory`. The following compiles against `prattail/src/presburger.rs`
(`LinearConstraint::from_gte(terms, rhs)`, `LinearConstraint::new(terms, rhs)`,
`PresburgerTheory::new(bit_width)`, and `IntAssignment::get(var) -> i64`):

```rust
use mettail_prattail::logict::{TheoryAlgebra, TheoryPred};
use mettail_prattail::presburger::{LinearConstraint, PresburgerTheory};
use mettail_prattail::symbolic::BooleanAlgebra;

let theory  = PresburgerTheory::new(8);          // 8-bit integer domain
let algebra = TheoryAlgebra::new(theory, 100);

// x₀ ≥ 3  ∧  x₀ ≤ 7
let pred = algebra.and(
    &TheoryPred::Atom(LinearConstraint::from_gte(vec![(0, 1)], 3)),
    &TheoryPred::Atom(LinearConstraint::new(vec![(0, 1)], 7)),   // `new` is the ≤ form
);

assert!(algebra.is_satisfiable(&pred));           // decided by NFA emptiness (label = empty)

let witness = algebra.witness(&pred).expect("should find a witness");
let v = witness.get(0);                            // IntAssignment::get → i64
assert!(v >= 3 && v <= 7);
```

Here `PresburgerTheory::label` returns `empty()`, so `Witness` (§7.3) reaches a
verdict by propagation and the line-4 witness check alone; `search_bound = 100`
never binds.

---

## 8. Quantified evaluation

Behavioral and theory guards are frequently *quantified*: `∀y ∈ nodes.
(reachable(x, y) ⇒ safe(y))`, for instance. The `logict` module provides a
first-order-logic AST (`QuantifiedFormula`) and two evaluators over it — a
two-valued one (`evaluate_quantified`) and a three-valued, theory-guided one
(`evaluate_quantified_with_theory`).

### 8.1 The `QuantifiedFormula` AST

```text
QuantifiedFormula ::= Atom    { relation: String, args: Vec<QuantifiedArg> }
                   |  And     (QuantifiedFormula, QuantifiedFormula)
                   |  Or      (QuantifiedFormula, QuantifiedFormula)
                   |  Not     (QuantifiedFormula)
                   |  Implies (QuantifiedFormula, QuantifiedFormula)     ▷ sugar for ¬a ∨ b
                   |  ForAll  { var: String, domain: QuantifiedDomain, body }
                   |  Exists  { var: String, domain: QuantifiedDomain, body }

QuantifiedArg     ::= Var(String)          ▷ resolved from the environment
                   |  Constant(String)      ▷ a literal value

QuantifiedDomain  ::= Relation(String)                          ▷ all tuples of a relation (T1/T2)
                   |  Bounded { relation: String, limit: usize } ▷ at most `limit` tuples (T3)
```

Builders mirror the variants: `QuantifiedFormula::{atom, and, or, not, implies,
forall, exists}` and `QuantifiedArg::{var, constant}`. The type implements
`Display` (rendering with Unicode `∧ ∨ ¬ ⇒ ∀ ∃ ∈`, and `Bounded` as
`relation[≤limit]`) and `free_vars` (the set of variables not bound by an
enclosing quantifier). For example, `QuantifiedFormula::forall("x",
QuantifiedDomain::Relation("items".into()), atom("positive", [var("x")]))`
displays as `∀x ∈ items. positive(x)`.

> **Codegen-shorthand caveat.** The macro layer
> (`ast/src/language/model.rs`, `macros/src/gen/runtime/wpda_codegen/refinement.rs`)
> emits constructor shorthands `nforall` / `nexists` / `natom` / `nand` / `nor`
> / `nnot` / `nimplies` / `nn` / `nmultiset_partitions`. **None of those names
> resolve in `prattail/src/`.** The real, public API is exactly the
> `QuantifiedFormula::{forall, exists, atom, and, or, not, implies}` /
> `QuantifiedArg::{var, constant}` set above, together with `evaluate_quantified`
> and `multiset_partitions`. Treat the `n…` shorthands as a generated-code
> reference only; they do not name any present `prattail` symbol.

### 8.2 `evaluate_quantified` — two-valued evaluation

`evaluate_quantified` evaluates a closed formula against caller-supplied
relations and returns a `bool`:

```rust
pub fn evaluate_quantified<F, G>(
    formula: &QuantifiedFormula,
    env: &HashMap<String, String>,
    relation_query: &F,        // (relation, resolved_args) → bool
    domain_enumerate: &G,      // relation → Vec<Vec<String>>  (its tuples)
    bound: usize,              // cap for Bounded domains
) -> bool
where F: Fn(&str, &[String]) -> bool,
      G: Fn(&str) -> Vec<Vec<String>>;
```

**Algorithm `EvaluateQuantified`** *(logict.rs:780–850)*

```text
⟨EvaluateQuantified(φ, env, query, enum, bound) → bool⟩ ≡
  1.  case φ of
  2.    Atom(R, args):     resolved ← map (resolve via env / constant) over args
  3.                       return query(R, resolved)
  4.    And(a, b):         return Eval(a) ∧ Eval(b)          ▷ short-circuit
  5.    Or(a, b):          return Eval(a) ∨ Eval(b)          ▷ short-circuit
  6.    Not(a):            return ¬ Eval(a)
  7.    Implies(a, b):     return ¬ Eval(a) ∨ Eval(b)
  8.    ForAll(x, D, body): tuples ← EnumerateDomain(D, enum, bound)
  9.                        return ∀ t ∈ tuples. Eval(body[x ↦ t.first])
 10.    Exists(x, D, body): tuples ← EnumerateDomain(D, enum, bound)
 11.                        return ∃ t ∈ tuples. Eval(body[x ↦ t.first])
```

where `EnumerateDomain(Relation(r)) = enum(r)` and
`EnumerateDomain(Bounded{r, limit}) = enum(r).take(min(limit, bound))`. A
quantifier binds `x` to the *first column* of each tuple (the common projection
for guards); multi-column relations are queried positionally via `Atom`.

> **How this connects to the logic monad — precisely.** `evaluate_quantified`
> does **not** construct a `LogicStream` per quantifier. It recurses directly
> over the *materialized* `Vec<Vec<String>>` returned by `domain_enumerate`,
> using Rust's `Iterator::all`/`any` for `∀`/`∃` and `take(min(limit, bound))`
> for a `Bounded` domain. The relationship to LogicT is **semantic**, not
> structural:
>
> - the closed-world reading of negation that makes `∀x. φ ≡ ¬∃x. ¬φ` hold is
>   exactly the `gnot` (negation-as-finite-failure) discipline of §4 — the
>   crate's tests `gnot_equivalence_forall_not_exists_not` and
>   `gnot_equivalence_exists_not_forall_not` assert these De Morgan dualities
>   over the evaluator; and
> - the `Bounded`-domain truncation mirrors `collect_bounded`'s finite budget.
>
> The monad backs this layer *semantically*; it backs `TheoryAlgebra::witness`
> and `multiset_partitions` *literally* (true fair search). The fairness of §3.4
> matters at the `witness` layer *beneath* a theory-guided quantifier (§8.4), not
> in the plain tuple enumeration here.

`ForAll` over an empty domain returns `true` (vacuous `⊤`); `Exists` over an
empty domain returns `false` (`⊥`). These are pinned by
`evaluate_empty_domain_forall_vacuous` and `evaluate_empty_domain_exists_false`.

### 8.3 `TriState` — three-valued (Kleene) logic

When the domain is undecidable or the search budget is exhausted, "unknown" is
the only honest verdict. `TriState` is the in-crate three-valued logic that
carries it. It is the **twin of `Sat3`** used at the substrate level
([13 §3](../../../../docs/architecture/symbolic-predicates/13-constraint-theory-engine.md)):
where `Sat3` is `{ Sat, Unsat, DontKnow }`, `TriState` is `{ True, False,
Unknown }`, with the same Kleene operators.

```rust
pub enum TriState { True, False, Unknown }
```

The connectives are **Kleene's strong three-valued logic**:

`∧` (`TriState::and`):

| `∧` | `True` | `False` | `Unknown` |
|---|---|---|---|
| **`True`** | `True` | `False` | `Unknown` |
| **`False`** | `False` | `False` | `False` |
| **`Unknown`** | `Unknown` | `False` | `Unknown` |

`∨` (`TriState::or`):

| `∨` | `True` | `False` | `Unknown` |
|---|---|---|---|
| **`True`** | `True` | `True` | `True` |
| **`False`** | `True` | `False` | `Unknown` |
| **`Unknown`** | `True` | `Unknown` | `Unknown` |

`¬` (`TriState::not`): `¬True = False`, `¬False = True`, `¬Unknown = Unknown`.

`⇒` (`TriState::implies`) is defined as `a ⇒ b ≡ ¬a ∨ b`, so e.g.
`False ⇒ anything = True` and `Unknown ⇒ True = True`. Two conversions close the
type:

- `into_safe_bool()` collapses `True → true` and **everything else → false** —
  the "safe-fail" default that *rejects* on `Unknown` rather than wrongly
  admitting. This is the run-time mirror of the reject-safe posture of the
  algebra pyramid.
- `From<bool>` lifts `true → True`, `false → False`.

The tables above are asserted exactly by the tests `tristate_kleene_and`,
`tristate_kleene_or`, `tristate_negation`, `tristate_implies`, and
`tristate_safe_bool_collapse`.

### 8.4 `evaluate_quantified_with_theory` — theory-guided, three-valued

This variant walks the same AST but threads a `ConstraintTheory` and returns a
`TriState`:

```rust
pub fn evaluate_quantified_with_theory<T, F, G>(
    formula: &QuantifiedFormula,
    theory: &T,                // a ConstraintTheory
    relation_query: &F,
    domain_enumerate: &G,
    env: &HashMap<String, String>,
    bound: usize,
) -> TriState
where T: ConstraintTheory, F: Fn(&str, &[String]) -> bool, G: Fn(&str) -> Vec<Vec<String>>;
```

**Algorithm `EvaluateQuantifiedWithTheory`** *(logict.rs:972–1144)*

```text
⟨EvalT(φ, theory, query, enum, env, bound) → TriState⟩ ≡
  1.  case φ of
  2.    Atom(R, args):     return TriState::from( query(R, resolved(args, env)) )
  3.    And(a, b):         ra ← EvalT(a); if ra = False then return False
  4.                       rb ← EvalT(b); return ra.and(rb)            ▷ Kleene ∧
  5.    Or(a, b):          ra ← EvalT(a); if ra = True  then return True
  6.                       rb ← EvalT(b); return ra.or(rb)             ▷ Kleene ∨
  7.    Not(inner):        return EvalT(inner).not()
  8.    Implies(a, b):     return EvalT(a).implies(EvalT(b))
  9.    ForAll(x, D, body): tuples ← EnumerateDomain(D, enum, bound)
 10.                        if tuples = ∅ then return True             ▷ ∀x∈∅. φ ≡ ⊤
 11.                        had_unknown ← false
 12.                        for t in tuples:
 13.                            case EvalT(body[x ↦ t.first]) of
 14.                              False:   return False                ▷ counterexample ⇒ definite ⊥
 15.                              Unknown: had_unknown ← true
 16.                              True:    continue
 17.                        return had_unknown ? Unknown : True
 18.    Exists(x, D, body): tuples ← EnumerateDomain(D, enum, bound)
 19.                        if tuples = ∅ then return False            ▷ ∃x∈∅. φ ≡ ⊥
 20.                        had_unknown ← false
 21.                        for t in tuples:
 22.                            case EvalT(body[x ↦ t.first]) of
 23.                              True:    return True                 ▷ witness ⇒ definite ⊤
 24.                              Unknown: had_unknown ← true
 25.                              False:   continue
 26.                        return had_unknown ? Unknown : False
```

The theory's role is to act as a **sound over-approximation**: the
monomorphization is kept honest by touching `theory.empty_store()` (so
theory-specific code is actually emitted), and a future theory can refine an
atom to `False` when its propagation makes the atom inconsistent regardless of
the extensional `relation_query`. The `Unknown` verdict is *produced* exactly by
the `had_unknown` accumulators on lines 11/17 and 20/26: a `ForAll` returns
`Unknown` when no `False` counterexample was found but at least one body
evaluation was `Unknown`; symmetrically for `Exists`. Empty-domain cases are the
classical `⊤`/`⊥` (lines 10, 19), asserted by
`evaluate_with_theory_forall_empty_domain_is_true` and
`evaluate_with_theory_exists_empty_domain_is_false`. A guard pipeline then
collapses the verdict with `into_safe_bool` (`Unknown → false`), which is what
makes the engine *reject-safe* end-to-end.

---

## 9. Theory combination

Two decidable theories over a shared, enumerable domain combine into a single
effective Boolean algebra by **joint search**: the LogicT realization
*interleaves* the two theories' constraint streams and labels them under the
shared bounded budget. Concretely, the combined satisfiability check threads a
candidate assignment through both theories' `propagate`/`witness`, using
`interleave` for the disjunctive choices and `fair_conjoin` for the conjunctive
threading, exactly as `CollectConstraints` does for a single theory (§7.2).

This is the **base case** of the Nelson–Oppen combination method
([Nelson & Oppen, 1979](#14-references)): cooperation over a *shared domain* by
joint search. It is **not** the full Nelson–Oppen equality-exchange procedure —
the engine does not yet propagate entailed equalities between the theories'
signatures (the convex/stably-infinite machinery). The documentation states this
limitation plainly rather than implying the general procedure. The proposed
surface syntax for combination is `arithmetic <+> text`
([06 §3.8](../../../../docs/architecture/symbolic-predicates/06-guard-syntax-and-extensions.md)).

The mechanized counterpart is
[`TheoryCombination.v`](../../../../formal/rocq/symbolic_algebra/theories/TheoryCombination.v):
`combined_eba_laws`, with `csat_sound` and `csat_complete`, proves that the
joint-search combination is itself an effective Boolean algebra (the base-case
soundness/completeness), surveyed in
[10 §2.1](../../../../docs/architecture/symbolic-predicates/10-formal-verification-and-tests.md).

---

## 10. AC-matching: multiset partitions

Associative-commutative (AC) matching — matching a pattern against a *bag* of
operands where order and grouping are irrelevant — reduces to enumerating the
ways to select `k` elements (with multiplicity) from a multiset. The `logict`
module provides this as a fair `LogicStream`, which is how the behavioral
predicate `BehavioralPred::AcMatch` enumerates candidate splits.

### 10.1 `MultisetPartition`

```rust
pub struct MultisetPartition<T: Clone + Eq + Hash> {
    /// Selected elements with their multiplicities.
    pub selected: Vec<(T, usize)>,
    /// Remaining elements after selection.
    pub remainder: Vec<(T, usize)>,
    /// Total count of selected elements (Σ of selected multiplicities).
    pub selected_count: usize,
}
```

with the invariants (asserted by `partition_sum_invariant`,
`partition_per_element_count_invariant`):

```text
selected_count = Σ_{(_,c) ∈ selected} c
∀ element e.  count(selected, e) + count(remainder, e) = count(source, e)
selected_count + Σ_{(_,c) ∈ remainder} c = source_count
```

### 10.2 `multiset_partitions` — the fair enumerator

```rust
pub fn multiset_partitions<T>(items: &[(T, usize)], k: usize)
    -> LogicStream<MultisetPartition<T>>
where T: Clone + Eq + Hash + Send + 'static;
```

It recurses over distinct elements, choosing how many copies `q ∈ 0..=min(count,
remaining)` of each element to include, and **interleaves** the per-`q`
sub-streams so that selections drawing on *later* elements are not starved:

**Algorithm `MultisetPartitions`** *(logict.rs:1459–1551)*

```text
⟨Partitions(items, start, remaining) → LogicStream<MultisetPartition>⟩ ≡
  1.  if remaining = 0:                                  ▷ nothing left to pick
  2.      return unit({ selected: ∅,
  3.                     remainder: nonzero tail of items[start..],
  4.                     selected_count: 0 })
  5.  if start ≥ |items|:           return empty()        ▷ ran out of element kinds
  6.  available ← Σ counts of items[start..]
  7.  if available < remaining:     return empty()        ▷ not enough copies remain
  8.  (elem, count) ← items[start]
  9.  acc ← empty()
 10.  for q in 0 ..= min(count, remaining):               ▷ take q copies of `elem`
 11.      sub ← Partitions(items, start+1, remaining − q)
 12.      merged ← map over sub, splicing `elem` into selected (q) / remainder (count−q)
 13.      acc ← interleave(acc, merged)                   ▷ fair across the choices of q
 14.  return acc
```

`multiset_partitions(items, k)` calls `Partitions(items, 0, k)`. Duplicate-free
enumeration is guaranteed because element index `i` is never reconsidered after
advancing to `i+1` (test `partition_no_duplicates`). The combinatorial identity
`|partitions(M, k)| = |partitions(M, n−k)|` (selecting `k` is dual to leaving
`n−k`) holds and is checked by `partition_complement_symmetry`.

### 10.3 `multiset_select` — the bounded convenience wrapper

```rust
pub fn multiset_select<T>(items: &[(T, usize)], k: usize, bound: usize)
    -> Vec<MultisetPartition<T>>
where T: Clone + Eq + Hash + Send + 'static;
```

This is simply `multiset_partitions(items, k).collect_bounded(bound)` — the
direct-`Vec` form for AC-match guard evaluation, where `bound` is the `T3` safety
cap. Worked examples: for `items = [('A', 3), ('B', 2)]` and `k = 2`, there are
three partitions (`{A:2}`, `{A:1, B:1}`, `{B:2}`); for `[('A',1),('B',1),('C',1)]`
and `k = 2`, there are `C(3,2) = 3`.

---

## 11. Integration with the substrate

This document is the engine reference; the *integration story* — how `logict`
sits beneath the symbolic-predicate substrate, which guard-syntax forms lower
into `QuantifiedFormula`/`TheoryPred`, how a `theories { name = T for [Cat] }`
registration becomes a usable guard algebra, and how the engine's verdict earns a
**tier** and **quality** that the fail-closed flip gate acts on — is told, with
four rendered figures, in
[13 — The Constraint-Theory Engine: LogicT Under the Substrate](../../../../docs/architecture/symbolic-predicates/13-constraint-theory-engine.md).
The essential bridges, in one table, so a reader need not chase them:

| Engine artifact (this doc) | Substrate role | Where |
|---|---|---|
| `TheoryAlgebra<T> : BooleanAlgebra` (§7) | makes a registered theory a reusable guard algebra → `SymbolicAutomaton`, minterms, determinization | [13 §2](../../../../docs/architecture/symbolic-predicates/13-constraint-theory-engine.md), [02](../../../../docs/architecture/symbolic-predicates/02-effective-boolean-algebra.md) |
| `evaluate_quantified*` → `TriState` (§8) | quantified-guard verdict, three-valued | [13 §3](../../../../docs/architecture/symbolic-predicates/13-constraint-theory-engine.md), [06 §2.3.1](../../../../docs/architecture/symbolic-predicates/06-guard-syntax-and-extensions.md) |
| `TriState` ↔ `Sat3`; `into_safe_bool` (§8.3) | reject-safe collapse feeding the flip gate | [13 §5](../../../../docs/architecture/symbolic-predicates/13-constraint-theory-engine.md), [05](../../../../docs/architecture/symbolic-predicates/05-algebra-pyramid-and-decidability.md), [12](../../../../docs/architecture/symbolic-predicates/12-heyting-behavioral-logic.md) |
| joint-search combination (§9) | Nelson–Oppen base-case EBA | `TheoryCombination.v`, [10 §2.1](../../../../docs/architecture/symbolic-predicates/10-formal-verification-and-tests.md) |
| `multiset_partitions` (§10) | `BehavioralPred::AcMatch` enumeration | [13 §1](../../../../docs/architecture/symbolic-predicates/13-constraint-theory-engine.md) |
| `collect_bounded(search_bound)` (§4, §7.3) | the resource meter; tier T3 boundary | `LT01` (§13), [05 §6](../../../../docs/architecture/symbolic-predicates/05-algebra-pyramid-and-decidability.md) |

---

## 12. Performance characteristics

| Operation | Complexity | Notes |
|---|---|---|
| `msplit` | `O(1)` amortized | One `VecDeque::pop_front`, plus forcing at most one `Suspended` thunk. |
| `mplus(b)` | `O(\|b\|)` | Extends the deque with all branches of `b`. |
| `interleave(b)` | `O(\|self\| + \|b\|)` | Splices the two branch queues element-by-element (no thunk forced). |
| `fair_conjoin(f)` | `O(\|self\| · \|f(x)\|)` | Applies `f` to each answer, folds by `interleave`. |
| `collect_bounded(n)` | `O(n · cost(msplit))` | At most `n` `msplit` calls. The bounded resource meter. |
| `collect_all()` | `O(\|stream\| · cost(msplit))` | **Diverges** on an infinite stream — §4.1 warning. |
| `ifte` | `O(cost(msplit) + then/else)` | One `msplit` for the test. |
| `once` | `O(cost(msplit))` | One `msplit`, discard the remainder. |
| `gnot` | `O(cost(msplit))` | One `msplit` to check emptiness. |
| `into_iter().next()` | `O(cost(msplit))` per step | Lazy; no eager collection. |

**Memory.** Each `Branch::Suspended` is one `Box<dyn FnOnce>` (a fat pointer of
two words plus the boxed closure's captured state). The `VecDeque` grows
amortized-`O(1)`. For a bounded search, peak memory is proportional to the
search bound times the average closure size, plus the live frontier of branches.
Constructors preallocate where the size is known: `unit` and `suspend` reserve
capacity `1`, and `interleave` reserves `|self| + |other|` up front, in keeping
with the project's preallocation practice. The `bench_logict` target tracks the
hot paths (`msplit`, `interleave`, `fair_conjoin`, `multiset_partitions`).

---

## 13. Diagnostics

The bounded fair search is *incomplete by construction*: when a theory's `label`
(or an AC enumeration) produces more alternatives than `search_bound` admits, the
search is truncated and the engine reports **`Unknown`** rather than `Unsat`.
That truncation is surfaced as the lint
[`LT01` — `logict-search-bound-exceeded`](../../diagnostics/logict/LT01.md):

- **Severity:** Warning (a *possibly* missed solution, not a definite failure) —
  because a truncated search may still have a witness beyond the explored
  frontier, the honest verdict is `Unknown`, never `Unsat`.
- **What it means:** `label()` produced more alternatives than `search_bound`
  allows; the global budget (a gas meter across *all* choice points, not
  per-point) was exhausted.
- **Common causes:** a genuinely deep search space, a divergent search (e.g. a
  recursive `custom_match` pattern that yields an infinite stream), or
  inefficient labeling order that buries the solution.
- **Remedies:** raise `search_bound`, simplify the constraint, or add pruning
  constraints earlier so the witness surfaces within budget.

Because a *decidable* theory returns an empty `label`, `LT01` can only fire for
theories that genuinely search (the `UnificationTheory` extended-match case,
user-defined searching theories, and large AC enumerations). It is the
diagnostic face of the `collect_bounded(search_bound)` resource gates in
`Witness` (§7.3). The definitive (bound-free) unsatisfiability lints of the
sibling theories — `PB01` (Presburger), `UN01` (unification), `SL01`
(subtype-lattice) — are the *complementary* signal: a hard `Unsat`, not a
budget-limited `Unknown`.

---

## 14. References

- Kiselyov, O., Shan, C., Friedman, D. P. & Sabry, A. (2005). "Backtracking,
  Interleaving, and Terminating Monad Transformers." *Proceedings of the Tenth
  ACM SIGPLAN International Conference on Functional Programming (ICFP 2005)*,
  pp. 192–203. DOI: [10.1145/1086365.1086390](https://doi.org/10.1145/1086365.1086390).
  *(The LogicT logic monad: `msplit`, fair `interleave`/`≫-`, `ifte`, `once`,
  and negation-as-failure — the source of every operator in §3–§4.)*
- Hemann, J. & Friedman, D. P. (2013). "µKanren: A Minimal Functional Core for
  Relational Programming." *Proceedings of the 2013 Workshop on Scheme and
  Functional Programming (Scheme Workshop 2013)*. *(The relational-programming
  lineage; no DOI assigned by the venue.)*
- Nelson, G. & Oppen, D. C. (1979). "Simplification by Cooperating Decision
  Procedures." *ACM Transactions on Programming Languages and Systems (TOPLAS)*,
  1(2), pp. 245–257. DOI: [10.1145/357073.357079](https://doi.org/10.1145/357073.357079).
  *(The theory-combination method; §9 implements its shared-domain base case.)*

**Companion documents (this repository):**

- [13 — The Constraint-Theory Engine: LogicT Under the Substrate](../../../../docs/architecture/symbolic-predicates/13-constraint-theory-engine.md)
  — integration narrative and the four figures.
- [10 — Formal Verification and Tests](../../../../docs/architecture/symbolic-predicates/10-formal-verification-and-tests.md)
  — the proof matrix, including `TheoryCombination.v`.
- [02 — Effective Boolean Algebra](../../../../docs/architecture/symbolic-predicates/02-effective-boolean-algebra.md)
  and [05 — Algebra Pyramid and Decidability](../../../../docs/architecture/symbolic-predicates/05-algebra-pyramid-and-decidability.md)
  — the abstract algebra and the `Sat3`/tier frame this engine populates.
- [`LT01` — `logict-search-bound-exceeded`](../../diagnostics/logict/LT01.md)
  — the bounded-search diagnostic.
