# Dovetail extractor (Increment 5) — exact lazy best-first derivation enumeration

> Plan-agent design (2026-06-09). `dovetail/src/extract.rs`. THE correctness-critical
> piece: it must **miss nothing**. Governing invariant (from the implementation plan):
> any technique is admissible **iff it provably misses no result**; demand only DEFERS
> (resumable to exhaustion); the only removal is by **evidence** (here: composed weight =
> semiring `0̄`); weight ORDERS, never PRUNES; an **admissible** A*/KA* heuristic is
> desirable, a lossy beam/cutoff is forbidden.

## Algorithm — Huang & Chiang 2005 **Algorithm 3** (exact lazy k-best), NOT cube-pruning
Each e-class `q` = a hypergraph vertex; each e-node `f(c1..cn)` in `q` = a hyperedge with
local weight `weigh(e)`. A derivation = pick one hyperedge + one derivation per child;
weight = `weigh(e) ⊗ ⊗ᵢ weight(dᵢ)`. Per class, a memoized **best-first stream** `built:
Vec<Rc<Derivation>>` extended on demand from a min-heap `cand` of candidates `(edge_idx,
ranks)` where `ranks[i]` indexes child i's stream. Pop the min; build it (pull each child's
`kth(cᵢ, ranks[i])` — recursion); push successors that bump one child's rank by 1; dedup
candidates via `seen:(edge_idx,ranks)`. Leaves (arity 0) seed a single candidate.

**No-miss argument:** for a fixed edge of arity n, its derivations are exactly `ℕⁿ`
(children inductively complete by acyclic structural induction). The heap performs
best-first lattice traversal of `ℕⁿ` from `0ⁿ`, each point enqueued once (`seen`), so ALL
derivations of `q` (= `⨆ₑ ℕ^arity(e)`) are eventually produced — exhaustive-on-demand.
**Best-first order** holds under the **monotonicity precondition (MON):** `⊗` is monotone
non-decreasing in each argument w.r.t. the order. Tropical (`⊗=+`) satisfies MON; for
`LexicographicWeight`, `times` left-projects the tiebreak fields so only the primary varies
with child rank — MON holds on the varied axis. The Rust API exposes this as
`MonotoneBestOrder`, a sealed marker implemented only for checked weight types.

## Weight order — `BestOrder` trait (NOT changing the semiring crate)
`Semiring` is `Copy + PartialEq` but NOT `Ord`. Both production weights already impl `Ord`
("smaller=better"): `rigail::TropicalWeight` (via `f64::total_cmp`, NaN-safe) and
`rigail::LexicographicWeight` (lexicographic). So:
```rust
pub trait BestOrder: Semiring { fn cmp_best(&self, o: &Self) -> Ordering; }
impl<W: Semiring + Ord> BestOrder for W { fn cmp_best(&self,o:&Self)->Ordering { self.cmp(o) } }
```
Heap key = `OrdKey { w, key: ContentKey }` ordered `w.cmp_best(...).then(key.cmp(...))` —
the total `(weight, ContentKey)` tiebreak so **equal-weight DISTINCT derivations both
survive** (popped consecutively, both pushed). Min-heap via `BinaryHeap<Reverse<…>>`.

## Derivation type
```rust
pub struct Derivation<L, W> {
    pub op: L, pub class: EClassId,
    pub children: Vec<Rc<Derivation<L, W>>>,
    pub weight: W, pub key: ContentKey,    // exact, injective tree key
}
```
Tree key = `op.write_content` then `write_ordered_framed(child.key)` per child — injective
(distinct trees ⇒ distinct keys), so the `built.last().key == d.key` check drops only TRUE
duplicates, never two distinct equal-weight derivations.

## `0̄` exclusion — the ONLY removal
After building `d`, if `d.weight.is_zero()` skip the `built.push` (but STILL push successors).
Semantic refutation, never a heuristic prune.

## Borrow-safe memoized mutual recursion + cycle guard
Per-class `ClassState { initialized, exhausted, on_stack, built, cand, seen }` in
`HashMap<EClassId, ClassState>`. `kth(&mut self, q, k)` recurses into `kth(child, rank)`;
discipline: never hold a `state[q]` borrow across the recursive call — pop in a short
scope, drop the borrow, recurse to pull child `Rc`s (cloned out), re-acquire to push. Edge
data (`op`, `weigh`, child classes) read from the e-graph (a different object than
`state`) + copied out before recursing. **Cycle guard:** `on_stack` flag — a back-edge
child is treated as "no derivation at this rank" (combination returns None) so cyclic
classes yield only acyclic derivations (sound but bounded for cyclic k>=2). Cyclic inside
weights / 1-best are exact via `compute_inside_closed`; exhaustive cyclic k-best remains
bounded and is surfaced by `ExtractionCompleteness::BoundedByCycleCut` and
`had_cycle_cut()`. Increment 5 is ACYCLIC-scoped (guard never fires on acyclic input).

## Public API
```rust
impl<'g,L,W,F> Extractor<'g,L,W,F>
where L: Clone+Eq+Hash+SemanticHash, W: MonotoneBestOrder, F: Fn(&ENode<L>)->W {
    pub fn new(egraph: &'g EGraph<L>, weigh: F) -> Self;
    pub fn with_heuristic(self) -> Self where W: CommutativeStarSemiring;
    pub fn kth(&mut self, root: EClassId, k: usize)
        -> Extraction<Option<Rc<Derivation<L,W>>>>;
    pub fn derivations(&mut self, root) -> Derivations<'_, 'g, L, W, F>;
    pub fn completeness(&self) -> ExtractionCompleteness;
    pub fn had_cycle_cut(&self) -> bool;
}

impl<'a,'g,L,W,F> Derivations<'a,'g,L,W,F> {
    pub fn next_checked(&mut self) -> ExtractionStep<Rc<Derivation<L,W>>>;
    pub fn collect_checked(self) -> Extraction<Vec<Rc<Derivation<L,W>>>>;
}
```
`Derivations` intentionally does **not** implement `Iterator`: completeness is terminal
metadata, not item-level fallibility. Callers step with `next_checked()` or collect with
`collect_checked()`, so the `ExtractionCompleteness` status cannot be silently dropped.
Heuristic is OPTIONAL: baseline is provably exact without it; it only reorders exploration
(verified by a heuristic-invariance test). No beam/cutoff anywhere.

## No-miss test suite (the empirical verification)
T1 single leaf; **T2 hand-built ambiguous (THE gating test):** merge a(5),b(3),c(3) into one
class ⇒ `derivations` yields exactly [w3, w3, w5], two distinct w3 keys BOTH present,
`kth(q,3)=None`; T3 cartesian product (ambiguous child × two edges) ⇒ exactly 4, weights
[4,4,7,7], all keys distinct; T4 `0̄` excluded (incl. `0̄`-child poisons parent); T5
resumability/random-access/idempotent-past-exhaustion; T6 `LexicographicWeight` tiebreak;
T7 determinism (run twice, identical key sequence); T8 cycle safety (terminates, no panic,
`had_cycle_cut`); T9 heuristic invariance (with/without `with_heuristic` ⇒ identical output).

## FV — `dovetail/formal/rocq/theories/Extraction/`
`NBestExtraction.v` proves the selection/order layer: only `0̄` candidates are removed,
every non-`0̄` candidate survives, equal-weight distinct alternatives both survive,
demand prefixes are monotone, the stream exhausts on demand, and the ordered output is a
sorted permutation of the kept candidates. `LazyFrontierOrder.v` proves the lazy heap
frontier emits a sorted stream when successor rank bumps cannot improve the candidate, and
that emitted elements plus the final frontier are a permutation of the initial frontier plus
generated successors.
`EnumerationCompleteness.v` proves the hypergraph-recursion layer: every
hyperedge/rank-vector product point is enumerated. `OrderPreservingFraming.v` proves the
ordered child-key framing is prefix-free, injective, and lex-order-preserving.
`ExtractionOutcome.v` and `CycleCutBoundary.v` model the Rust
`Extraction<T> { value, completeness }` / `ExtractionStep::Done` boundary and prove a cycle
cut maps to `BoundedByCycleCut`, never a silent `Complete` claim. `ExactKeyDedup.v` proves
the exact-key dedup contracts used by `SemanticHash`.

## Implementation order
Implemented: BestOrder+OrdKey, Derivation+tree-key, ClassState/Candidate initialization,
candidate construction, `kth` loop (`0̄` filter + exact-key dup skip + cycle guard),
checked `derivations` stream (`next_checked`, `collect_checked`, no plain `Iterator`),
`with_heuristic`, `completeness`, `had_cycle_cut`, tests T1-T9, and the Rocq proof suite
under `dovetail/formal/rocq/theories/Extraction/`.
