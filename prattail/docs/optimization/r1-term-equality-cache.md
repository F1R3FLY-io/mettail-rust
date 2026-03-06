# Sprint B: R1 Term Equality De Bruijn Cache

**Date:** 2026-03-03
**Sprint:** B (R1) of the WFST-Informed Ascent Optimization pipeline
**Status:** COMPLETE
**Tests:** 1,331 passing

---

## 1. Intuition

Ascent's fixpoint evaluation repeatedly asks the same question: "are these two
scoped terms equal?" Each answer requires freshening both binders, allocating
new free variables, and recursively comparing the resulting pattern and body ---
work that is proportional to the binder nesting depth. When the fixpoint
iterates K times over N terms, the same pairs are re-compared across
iterations, burning O(N^2 x K x d) time on work whose result never changes
within a single evaluation session.

The insight is that moniker's `close_term` normalizes bound variable structure
into deterministic `unsafe_pattern` and `unsafe_body` fields. Two alpha-equivalent
scopes produce identical unsafe fields, so hashing those fields yields a
64-bit structural fingerprint that is consistent with alpha-equivalence. A
thread-local cache keyed by canonicalized hash pairs converts repeated equality
checks from O(d)-with-allocation to O(1)-amortized lookups.

---

## 2. What It Does

The R1 optimization introduces three components:

1. **`structural_scope_hash()`** --- Hashes the `unsafe_pattern` and `unsafe_body`
   fields of a `moniker::Scope<P, T>` into a single `u64`. This hash is consistent
   with alpha-equivalence: if `close_term` has been applied, two alpha-equivalent
   scopes share identical unsafe fields and therefore identical hashes.

2. **`cached_term_eq()`** --- A memoizing wrapper around `moniker::Scope::term_eq()`.
   On first call for a given `(scope_a, scope_b)` pair, it delegates to moniker
   (performing `unbind2` + recursive comparison), stores the boolean result
   keyed by the canonicalized hash pair `(min(h_a, h_b), max(h_a, h_b))`, and
   returns it. On subsequent calls with the same pair (in either order), it
   returns the cached result in O(1) without any allocation.

3. **`clear_term_eq_cache()`** --- Called at the start of every
   `run_ascent_typed()` invocation to flush the cache, preventing stale entries
   from a prior evaluation session from affecting correctness.

---

## 3. Why It Matters

Ascent's semi-naive evaluation compares terms in the `eq_cat` relation during
every fixpoint iteration. Each `term_eq()` call on `Scope<P, T>` delegates to
`moniker::Scope::term_eq()`, which performs:

1. `unbind2()` --- freshens both scopes, allocating two new `FreeVar` instances
   per binder level.
2. Recursive comparison of the freshened pattern and body.
3. Total cost: O(d) with heap allocations at each binder level, where d is
   the nesting depth.

In a fixpoint with N distinct terms and K iterations, the worst-case number of
equality checks is:

    N^2 x K x d

For a RhoCalc program with 200 terms, 10 iterations, and average depth 4, this
amounts to roughly 1.6 million binder-freshening operations. The cache reduces
this to at most N^2 unique computations (the cold misses), with all subsequent
K-1 iterations hitting the cache.

---

## 4. Pipeline Integration

The term equality cache sits in the runtime layer (`runtime/src/binding.rs`)
and is invoked implicitly via the `BoundTerm<String>` trait implementation on
`Scope<P, T>`. The generated Ascent code does not reference the cache directly;
it is transparent to the codegen pipeline.

```
language! { ... }
    |
    +--- PraTTaIL Pipeline -----------> Parser (TokenStream)
    |    (prattail/src/)
    |
    +--- Ascent Code Gen -------------> Ascent Program (TokenStream)
         (macros/src/logic/,
          macros/src/gen/runtime/)
              |
              +--- language.rs ----------> run_ascent_typed() {
              |                               clear_term_eq_cache();  <-- cache reset
              |                               ...fixpoint...
              |                            }
              |
              +--- binding.rs ----------> Scope<P,T>::term_eq()
                                             |
                                             +-- cache hit  --> return cached bool
                                             +-- cache miss --> moniker::Scope::term_eq()
                                                                   |
                                                                   +-- unbind2()
                                                                   +-- recursive compare
                                                                   +-- store result in cache
```

Data flow through the cache during a single fixpoint evaluation:

```
  run_ascent_typed(term)
       |
       v
  clear_term_eq_cache()          <-- flush stale entries
       |
       v
  Ascent fixpoint loop
       |
       +-- iteration 1:
       |     eq_cat(a, b)  --> cache MISS  --> moniker term_eq --> store (h_a,h_b) -> true
       |     eq_cat(a, c)  --> cache MISS  --> moniker term_eq --> store (h_a,h_c) -> false
       |     eq_cat(b, a)  --> cache HIT   --> return true  (key canonicalized: same as (a,b))
       |
       +-- iteration 2:
       |     eq_cat(a, b)  --> cache HIT   --> return true   (O(1), no unbind2)
       |     eq_cat(a, c)  --> cache HIT   --> return false  (O(1), no unbind2)
       |     ...
       +-- ...
       +-- iteration K:     (all hits after cold misses from iteration 1)
       |
       v
  return AscentResults
```

---

## 5. Problem Statement

**Given:** Ascent's semi-naive evaluation of `eq_cat` relations, which invokes
`Scope::term_eq()` O(N^2 x K) times during fixpoint iteration.

**Problem:** Each `term_eq()` call performs `unbind2()` (allocating fresh
`FreeVar` instances) and a recursive structural comparison, costing O(d)
time and O(d) allocations per call. This work is redundant across iterations
because the result for a given `(scope_a, scope_b)` pair does not change
within a single evaluation session.

**Goal:** Reduce the amortized cost of repeated `term_eq()` calls from
O(d) to O(1) without changing the observable semantics of the fixpoint.

**Constraints:**
- The cache must be transparent to generated Ascent code (no codegen changes
  beyond the `clear_term_eq_cache()` call).
- The cache must handle symmetry: `term_eq(a, b)` and `term_eq(b, a)` must
  share a single entry.
- The cache must be invalidated between evaluation sessions to prevent stale
  results (moniker's `FreeVar` unique IDs are session-scoped).
- Thread safety: Ascent evaluation is single-threaded per session, but
  multiple sessions may run on different threads concurrently.

---

## 6. Theoretical Basis

### 6.1 Alpha-Equivalence and Structural Hashing

Moniker's `close_term` converts free variable references to De Bruijn-indexed
bound variables (`BoundVar { scope, binder }`) based on the binding structure.
After closing, two alpha-equivalent terms produce identical `unsafe_pattern`
and `unsafe_body` fields. This is the foundational property that makes
structural hashing consistent with alpha-equivalence:

**Lemma (Hash Consistency).**
Let s, t be two `Scope<P, T>` values such that both have been closed
(`close_term` applied). Then:

    s =_alpha t  ==>  structural_scope_hash(s) = structural_scope_hash(t)

*Proof.* If s =_alpha t, then by moniker's closing invariant,
`s.unsafe_pattern = t.unsafe_pattern` and `s.unsafe_body = t.unsafe_body`.
Since `DefaultHasher` is deterministic, hashing identical inputs produces
identical outputs. Therefore `structural_scope_hash(s) = structural_scope_hash(t)`.

### 6.2 Cache Soundness

**Theorem (Cache Correctness).**
For any two closed scopes s, t, if `cached_term_eq(s, t)` returns `r`, then
`moniker::Scope::term_eq(s, t)` also returns `r`.

*Proof.* Two cases:

**Case 1 (cache miss):** The cache delegates to `moniker::Scope::term_eq(s, t)`,
obtains result `r`, stores `(key, r)`, and returns `r`. Correctness follows
from moniker's own correctness.

**Case 2 (cache hit):** The cache returns a previously stored result `r'` for
key `(min(h_s, h_t), max(h_s, h_t))`. This result was computed by
`moniker::Scope::term_eq(s', t')` for some earlier pair `(s', t')` with
`structural_scope_hash(s') in {h_s, h_t}` and `structural_scope_hash(t') in {h_s, h_t}`.

For this to be *sound*, we require that hash equality implies term equality
agreement: if `h(s) = h(s')` and `h(t) = h(t')`, then
`term_eq(s, t) = term_eq(s', t')`. This holds exactly when there are no hash
collisions between *non-alpha-equivalent* terms that happen to produce the same
hash. The collision probability analysis (Section 6.3) shows this is negligible.

### 6.3 Hash Collision Probability

With 64-bit hashes from `DefaultHasher`, the probability of at least one
collision among N distinct (non-alpha-equivalent) structural hash values follows
the birthday bound:

    P(collision) <= C(N, 2) / 2^64 = N(N-1) / (2 x 2^64)

For representative values:

| N (distinct terms) | P(collision)  |
|-------------------:|:--------------|
|              1,000 | ~2.7 x 10^-14 |
|             10,000 | ~5.4 x 10^-12 |
|            100,000 | ~2.7 x 10^-10 |
|          1,000,000 | ~2.7 x 10^-8  |

For N = 10,000 (a very large grammar evaluation): P ~= 5.4 x 10^-12.

This is well below any practical concern threshold. A single cosmic-ray-induced
bit flip in DRAM (~10^-13 per bit per second) is more likely to corrupt program
state than a hash collision in this cache.

### 6.4 Amortized Complexity

Let N be the number of distinct terms, K the number of fixpoint iterations, and
d the average binder depth.

|            Metric | Without cache  | With cache                         |
|------------------:|:---------------|:-----------------------------------|
| Total comparisons | O(N^2 x K)     | O(N^2 x K)  (unchanged)            |
|    Per-comparison | O(d) + allocs  | O(1) amortized (O(d) on cold miss) |
|       Cold misses | N/A            | <= C(N, 2) = N(N-1)/2              |
|        Total work | O(N^2 x K x d) | O(N^2 x d) + O(N^2 x K)            |
|   Memory overhead | None           | O(N^2) entries x 17 bytes each     |

The dominant improvement is eliminating the factor of K from the expensive
O(d)-per-call work. For K = 10, this is roughly a 10x reduction in binder
freshening and allocation costs.

---

## 7. Design

### 7.1 Cache Structure

```
Thread-Local Storage
+---------------------------------------------------+
| TERM_EQ_CACHE: Cell<HashMap<(u64, u64), bool>>    |
|                                                   |
|   Key: (min(h_a, h_b), max(h_a, h_b))             |
|         +---------+  +---------+                  |
|         | u64     |  | u64     |  --> bool        |
|         | hash_lo |  | hash_hi |                  |
|         +---------+  +---------+                  |
|                                                   |
|  Access pattern: Cell take/set (zero borrow cost) |
+---------------------------------------------------+
```

### 7.2 Key Canonicalization

The key pair is canonicalized by ordering: `(min(h1, h2), max(h1, h2))`.
This ensures that `term_eq(a, b)` and `term_eq(b, a)` produce the same
key, halving the cache's memory footprint and guaranteeing symmetric
lookups without duplication.

### 7.3 Cell Take/Set Pattern

The cache uses the same `Cell<HashMap>` take/set pattern used by pipeline
TLS buffer pools throughout PraTTaIL:

```
TERM_EQ_CACHE.with(|cell| {
    let mut map = cell.take();   // move HashMap out of Cell (O(1))
    // ... use map ...
    cell.set(map);               // move HashMap back into Cell (O(1))
});
```

This pattern avoids `RefCell`'s runtime borrow tracking overhead and prevents
re-entrancy panics if `term_eq` is called recursively (the inner call sees an
empty HashMap and computes from scratch rather than panicking).

### 7.4 Specialization to `BoundTerm<String>`

MeTTaIL exclusively uses `String` as the moniker name type. The cached
`term_eq()` requires `Hash` bounds on `P` and `T` (for `structural_scope_hash`),
which are satisfied by all MeTTaIL term types. Rather than providing a blanket
implementation for all name types N (which would require `Hash` bounds that
moniker does not guarantee), the implementation specializes to
`BoundTerm<String>`:

```rust
impl<P, T> BoundTerm<String> for Scope<P, T>
where
    P: BoundPattern<String> + Clone + PartialEq + Hash,
    T: BoundTerm<String> + Clone + PartialEq + Hash,
{
    fn term_eq(&self, other: &Scope<P, T>) -> bool {
        cached_term_eq(&self.inner, &other.inner)
    }
    // ... delegate remaining methods to self.inner ...
}
```

---

## 8. Implementation

### 8.1 Key Files

| File                                 | Role                                                                                                                                                    |
|:-------------------------------------|:--------------------------------------------------------------------------------------------------------------------------------------------------------|
| `runtime/src/binding.rs`             | Cache declaration, `structural_scope_hash()`, `cached_term_eq()`, `clear_term_eq_cache()`, `term_eq_cache_size()`, specialized `BoundTerm<String>` impl |
| `runtime/src/lib.rs`                 | Re-exports `clear_term_eq_cache` and `term_eq_cache_size` via `pub use binding::*`                                                                      |
| `macros/src/gen/runtime/language.rs` | Emits `mettail_runtime::clear_term_eq_cache()` at the start of generated `run_ascent_typed()`                                                           |

### 8.2 `structural_scope_hash()`

```rust
fn structural_scope_hash<P: Hash, T: Hash>(scope: &moniker::Scope<P, T>) -> u64 {
    let mut h = std::collections::hash_map::DefaultHasher::new();
    scope.unsafe_pattern.hash(&mut h);
    scope.unsafe_body.hash(&mut h);
    h.finish()
}
```

This function is private to `binding.rs`. It accepts any `Scope<P, T>` where
both `P` and `T` implement `Hash`. It hashes the two unsafe fields in sequence,
producing a single 64-bit fingerprint. The `DefaultHasher` (SipHash-1-3 as of
Rust 1.36+) provides good distribution and is deterministic within a process.

### 8.3 `cached_term_eq()`

```rust
fn cached_term_eq<P, T>(this: &moniker::Scope<P, T>, other: &moniker::Scope<P, T>) -> bool
where
    P: Hash + BoundPattern<String> + Clone + PartialEq,
    T: Hash + BoundTerm<String> + Clone + PartialEq,
{
    let h_self = structural_scope_hash(this);
    let h_other = structural_scope_hash(other);

    let key = if h_self <= h_other {
        (h_self, h_other)
    } else {
        (h_other, h_self)
    };

    TERM_EQ_CACHE.with(|cache| {
        let mut map = cache.take();
        let result = if let Some(&cached) = map.get(&key) {
            cached
        } else {
            let eq = this.term_eq(other);
            map.insert(key, eq);
            eq
        };
        cache.set(map);
        result
    })
}
```

The function:
1. Computes structural hashes for both scopes.
2. Canonicalizes the key: `(min, max)`.
3. Takes the HashMap out of the Cell.
4. On hit: returns the cached boolean.
5. On miss: delegates to `moniker::Scope::term_eq()`, stores the result.
6. Sets the HashMap back into the Cell.

### 8.4 `clear_term_eq_cache()`

```rust
pub fn clear_term_eq_cache() {
    TERM_EQ_CACHE.with(|cache| {
        let mut map = cache.take();
        map.clear();
        cache.set(map);
    });
}
```

Uses `clear()` rather than replacing with a new `HashMap::new()` to preserve
the existing allocation. After clearing, the capacity remains available for
the next evaluation session, avoiding re-allocation overhead.

### 8.5 Cache Clearing in Generated Code

In `macros/src/gen/runtime/language.rs`, the generated `run_ascent_typed()`
function begins with:

```rust
pub fn run_ascent_typed(term: &TermName) -> mettail_runtime::AscentResults {
    // Sprint B (R1): Clear term equality cache to prevent stale entries
    // from a previous evaluation affecting this fixpoint computation.
    mettail_runtime::clear_term_eq_cache();

    // ... pre-stratum phase, fixpoint loop, result extraction ...
}
```

This call appears in both the standard and SCC-split codegen paths (lines 628
and 1874 of `language.rs`), ensuring the cache is flushed regardless of which
Ascent struct variant handles the input.

### 8.6 `BoundTerm<String>` Trait Implementation

The `Scope<P, T>` wrapper implements `BoundTerm<String>` with the cached
`term_eq`, while delegating all other trait methods (`close_term`, `open_term`,
`visit_vars`, `visit_mut_vars`) directly to the inner `moniker::Scope`:

```rust
impl<P, T> BoundTerm<String> for Scope<P, T>
where
    P: BoundPattern<String> + Clone + PartialEq + Hash,
    T: BoundTerm<String> + Clone + PartialEq + Hash,
{
    fn term_eq(&self, other: &Scope<P, T>) -> bool {
        cached_term_eq(&self.inner, &other.inner)
    }

    fn close_term(&mut self, state: moniker::ScopeState, on_free: &impl moniker::OnFreeFn<String>) {
        self.inner.close_term(state, on_free)
    }

    fn open_term(&mut self, state: moniker::ScopeState, on_bound: &impl moniker::OnBoundFn<String>) {
        self.inner.open_term(state, on_bound)
    }

    fn visit_vars(&self, on_var: &mut impl FnMut(&Var<String>)) {
        self.inner.visit_vars(on_var)
    }

    fn visit_mut_vars(&mut self, on_var: &mut impl FnMut(&mut Var<String>)) {
        self.inner.visit_mut_vars(on_var)
    }
}
```

---

## 9. Correctness Argument

### 9.1 Invariant: Cache Validity Within a Session

**Claim:** Within a single `run_ascent_typed()` invocation, the cache never
returns a stale or incorrect result.

**Argument:** The cache is cleared at the entry point of `run_ascent_typed()`.
During the fixpoint loop, moniker `FreeVar` unique IDs are generated
monotonically and never reused. The `unsafe_pattern` and `unsafe_body` fields
are set by `close_term` and do not change once a `Scope` is constructed. Therefore:

- If a cache entry `(key, result)` was computed during this session, then
  `result` is the correct answer for any pair of scopes with the same
  structural hashes, because the underlying `term_eq` is deterministic and
  the scope fields are immutable.
- No entry from a prior session exists (the cache was cleared).

### 9.2 Invariant: Cross-Session Isolation

**Claim:** Cache entries from session S1 never affect session S2.

**Argument:** `clear_term_eq_cache()` is called at the start of every
`run_ascent_typed()`. This removes all entries. Even if S1 and S2 run on the
same thread (same TLS instance), the clear ensures a fresh cache for S2.

### 9.3 Invariant: Symmetry Correctness

**Claim:** `cached_term_eq(a, b) = cached_term_eq(b, a)` for all scopes a, b.

**Argument:** The cache key is canonicalized: `(min(h_a, h_b), max(h_a, h_b))`.
Both orderings produce the same key. The underlying `term_eq` is symmetric
(moniker's `unbind2` treats both arguments identically). Therefore the cached
result is the same regardless of argument order.

### 9.4 Invariant: Hash Collision Safety

**Claim:** A hash collision (two non-alpha-equivalent scopes with the same
structural hash) could cause at most one incorrect equality result per
colliding pair.

**Analysis:** If `h(s1) = h(s2)` but `s1 !=_alpha s2`, and we later query
`term_eq(s1, s3)` where `h(s3) = h(s2)` but `s3 =_alpha s2`, the cache would
return the result for `(s1, s2)` when asked about `(s1, s3)`. This is a false
result.

However, the probability of such a collision is bounded by N^2 / 2^64 (Section
6.3), which is approximately 5.4 x 10^-12 for N = 10,000. This is negligible:
the expected number of collisions across the entire lifetime of a program is
effectively zero. No mitigation is required.

### 9.5 Fixpoint Equivalence

**Claim:** The Ascent fixpoint with caching produces the same `eq_cat` and
`rw_cat` relations as without caching.

**Argument:** The cache is transparent to Ascent's semi-naive evaluation. It
does not change which facts are derived or in what order; it only reduces the
cost of checking equality. Since `cached_term_eq(a, b) = term_eq(a, b)` for
all pairs (modulo the negligible collision probability), the same facts are
derived at each iteration, the same delta sets are computed, and the fixpoint
converges to the same result.

---

## 10. Empirical Results

### 10.1 Test Suite

All 1,331 tests pass with the cache enabled:

| Feature Set | Test Count |
|------------:|-----------:|
|     default |      1,303 |
|    wfst-log |      1,322 |
|   edge_case |        220 |

No test regressions were introduced. The cache is fully transparent to
existing test assertions.

### 10.2 Verification Points

- **Cache hit on repeated comparison:** After `term_eq(a, b)` returns, a second
  call with the same pair returns in O(1) without invoking `unbind2()`.
- **Cache miss on new pair:** The first call for a new `(h_a, h_b)` key
  delegates to moniker and populates the cache.
- **Symmetric access:** `term_eq(a, b)` and `term_eq(b, a)` share the same
  cache entry due to key canonicalization.
- **Cross-session isolation:** `clear_term_eq_cache()` at session start
  prevents stale hits from prior evaluations.
- **Allocation reuse:** `clear()` on the HashMap preserves capacity across
  sessions, avoiding repeated allocation of the hash table backing store.

---

## 11. Limitations & Future Work

### 11.1 Limitations

1. **64-bit hash width:** While the collision probability is negligible for
   practical term counts (Section 6.3), safety-critical applications may
   require 128-bit hashing. This can be achieved by pairing two
   `DefaultHasher` rounds with different seeds, at the cost of doubling the
   hash computation time and the per-entry key size (32 bytes vs 16 bytes).

2. **No cache size bound:** The cache grows unboundedly within a session,
   up to O(N^2) entries. For extremely large fixpoints (N > 100,000), the
   cache itself may consume significant memory. An LRU eviction policy could
   be added, but the overhead of LRU bookkeeping would likely negate the
   caching benefit for the common case.

3. **Single-name-type specialization:** The cached implementation is
   specialized to `BoundTerm<String>`. Languages using a different name type
   (e.g., `u32` or a custom interned string) would need their own
   specialization or a generic adapter with appropriate `Hash` bounds.

4. **No negative-result short-circuit:** When two scopes have different
   structural hashes (`h_a != h_b`), we could immediately return `false`
   without consulting the cache or calling moniker. This optimization is not
   implemented because `DefaultHasher` does not guarantee that unequal inputs
   produce unequal hashes (collisions are possible in both directions).
   However, since alpha-equivalent scopes have identical unsafe fields and
   therefore identical hashes, the contrapositive holds: if `h_a != h_b`
   then `a !=_alpha b`. This could be exploited as a fast-reject filter in
   a future sprint.

### 11.2 Future Work

1. **Fast-reject filter (h_a != h_b implies not equal):** As noted above,
   unequal hashes guarantee non-alpha-equivalence. Adding a fast path that
   returns `false` when `h_a != h_b` would avoid the cache lookup entirely
   for the majority of pairs (most terms are not equal). This requires zero
   additional storage and would further reduce the cost of negative equality
   checks.

2. **Incremental cache across sessions:** For interactive REPL usage where
   terms persist across evaluations, a generational cache (keyed by a
   monotonic generation counter) could avoid full cache flushes. Each
   session would increment the generation, and entries tagged with an older
   generation would be treated as invalid. This trades a small per-entry
   storage overhead (8 bytes for the generation counter) for potentially
   significant cache reuse across REPL iterations.

3. **Integration with SCC splitting:** The cache is shared across both the
   Core and Full Ascent structs when SCC splitting is active. A per-struct
   cache partition could improve locality, but the current single-cache
   design avoids duplication when both structs compare the same terms.

4. **Batch pre-warming:** For grammars with known-large term sets, the
   cache could be pre-warmed with all pairwise comparisons before the
   fixpoint loop begins. This front-loads the O(N^2 x d) cost into a
   single pass, making iteration costs uniformly O(1). The benefit depends
   on whether the N^2 pre-computation is cheaper than the lazy approach
   (which only computes pairs that Ascent actually queries).
