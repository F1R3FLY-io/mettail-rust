# E-Graph Equality Saturation -- Compile-Time Term Equivalence Discovery

**Status:** PLANNED
**Feature gate:** `egraph`
**Dependencies:** `trs-analysis` (confluence integration)
**Key files:** `prattail/src/egraph.rs` (planned), `pipeline.rs` (integration), `lint.rs` (EG01--EG04)

---

## Theoretical Foundation

### Congruence Closure

An **e-graph** (equivalence graph) is a data structure that compactly represents
a set of terms and their equivalence classes under a congruence relation. The
central invariant is **congruence closure**: if two terms are equivalent, then
any subterms substituted into the same context must also be equivalent. Formally,
given a set of equations E over a term algebra T(F, V):

    a_1 = b_1, ..., a_n = b_n    implies    f(a_1, ..., a_n) = f(b_1, ..., b_n)

for every function symbol f in F. The e-graph maintains this closure
incrementally by merging equivalence classes and propagating congruence through
parent pointers.

The data structure consists of two interleaved components:

- **E-nodes**: represent function applications `f(c_1, ..., c_n)` where each
  `c_i` is an equivalence class identifier (not a concrete term). Two e-nodes
  are congruent if they have the same function symbol and their children belong
  to pairwise-equivalent classes.

- **E-classes**: equivalence classes of e-nodes. Each e-class has a canonical
  representative and a set of member e-nodes. The union-find structure supports
  near-constant-time `find()` and `union()` operations.

### Equality Saturation

**Equality saturation** (Tate et al., 2009; Willsey et al., 2021) is an
optimization technique that applies a set of rewrite rules to an e-graph until
no new equivalences can be discovered (the e-graph is *saturated*) or a resource
limit is reached. Unlike traditional rewriting, which destructively replaces a
matched term with its reduct, equality saturation *adds* the reduct to the
e-graph as an equivalent representation, preserving all prior representations.

The algorithm proceeds in iterative phases:

1. **Match**: find all rewrite rule left-hand-side patterns that match e-nodes
   in the current e-graph. Each match produces a substitution mapping pattern
   variables to e-class identifiers.

2. **Apply**: for each match, instantiate the right-hand-side pattern under the
   substitution and merge the resulting e-node's class with the matched e-node's
   class. This may trigger cascading congruence merges.

3. **Rebuild**: restore the congruence closure invariant after all merges.
   Deduplicate e-nodes whose children now belong to the same classes and
   propagate parent updates through the hashcons.

4. **Check**: if no new merges occurred in this iteration, the e-graph is
   saturated. If resource limits (max_nodes, max_iterations) are exceeded,
   stop with a non-convergence warning (EG03).

After saturation (or resource exhaustion), an **extraction** pass selects the
optimal representative term from each e-class according to a cost function.

The key insight from Willsey et al. (2021) -- the `egg` paper -- is that
equality saturation avoids the *phase-ordering problem*: rather than choosing
which rewrite to apply at each step (risking suboptimal local decisions), all
rewrites are applied simultaneously and the globally optimal result is extracted
afterward.

### Formal Properties

**Theorem (Soundness).** If the rewrite rules are sound equations (both sides
are semantically equivalent in the intended theory), then every equivalence
discovered by equality saturation is a valid semantic equivalence.

**Theorem (Monotonicity).** The e-graph grows monotonically: merging e-classes
never removes terms, only identifies them. This ensures that extraction always
has access to the original term as a candidate.

**Theorem (Termination guarantee).** With bounded max_nodes and max_iterations,
the algorithm always terminates. Without bounds, saturation may diverge for
non-terminating rewrite systems (hence EG03).

---

## Architecture Diagram

```
                        ┌──────────────────────────────────────────────────┐
                        │              E-Graph Module                      │
                        │                                                  │
                        │  ┌────────────────────────────────────────────┐  │
                        │  │            Union-Find                      │  │
                        │  │                                            │  │
                        │  │  find(id) -> ClassId                       │  │
                        │  │  union(a, b) -> ClassId                    │  │
                        │  │  path compression + union by rank          │  │
                        │  └──────────────────┬─────────────────────────┘  │
                        │                     │                            │
                        │  ┌──────────────────▼─────────────────────────┐  │
                        │  │           E-Class Table                     │  │
                        │  │                                            │  │
                        │  │  HashMap<ClassId, EClass>                   │  │
                        │  │  EClass { id, nodes: Vec<ENode>,           │  │
                        │  │           parents: Vec<(ENode, ClassId)> }  │  │
                        │  └──────────────────┬─────────────────────────┘  │
                        │                     │                            │
                        │  ┌──────────────────▼─────────────────────────┐  │
                        │  │           Hashcons (Memo Table)             │  │
                        │  │                                            │  │
                        │  │  HashMap<ENode, ClassId>                    │  │
                        │  │  Canonical lookup after rebuild             │  │
                        │  └──────────────────┬─────────────────────────┘  │
                        │                     │                            │
                        │  ┌──────────────────▼─────────────────────────┐  │
                        │  │           Pattern Matcher                   │  │
                        │  │                                            │  │
                        │  │  match_pattern(lhs, egraph) -> [Subst]     │  │
                        │  │  Relational e-matching (Willsey 2021)      │  │
                        │  └──────────────────┬─────────────────────────┘  │
                        │                     │                            │
                        │  ┌──────────────────▼─────────────────────────┐  │
                        │  │           Cost Extractors                   │  │
                        │  │                                            │  │
                        │  │  AstSize / AstDepth / WeightedCost         │  │
                        │  │  extract_best(class, cost_fn) -> Term      │  │
                        │  └────────────────────────────────────────────┘  │
                        └──────────────┬───────────────────────────────────┘
                                       │
              ┌────────────────────────┼────────────────────────┐
              │                        │                        │
    ┌─────────▼──────────┐  ┌─────────▼──────────┐  ┌──────────▼──────────┐
    │ Confluence          │  │ Pipeline            │  │ Lint                 │
    │ Integration         │  │ Integration         │  │ Integration          │
    │                     │  │                     │  │                      │
    │ T01 critical pairs  │  │ analyze_egraph()    │  │ EG01: equivalence    │
    │ -> joinability via  │  │ in pipeline.rs      │  │ EG02: simplifiable   │
    │ e-graph search      │  │ EgraphResult in ctx │  │ EG03: non-converge   │
    │                     │  │                     │  │ EG04: joinability    │
    └─────────────────────┘  └─────────────────────┘  └──────────────────────┘
```

---

## Data Flow

The e-graph operates on PraTTaIL's internal term representation. The full
data flow from grammar terms through e-graph analysis to optimized output is:

```
 Grammar Terms (AST constructors from language! macro)
        │
        ▼
 ┌──────────────┐    Recursive decomposition of each constructor's
 │ Term -> ENode │    fields into e-nodes. Each function symbol f with
 │               │    children [c1, ..., cn] becomes ENode(f, [c1, ..., cn]).
 └──────┬───────┘
        │
        ▼
 ┌──────────────┐    Each e-node is inserted into the hashcons table.
 │ ENode -> add()│    If a structurally identical e-node already exists,
 │               │    the existing class id is returned. Otherwise, a
 │               │    new e-class is created containing this single e-node.
 └──────┬───────┘
        │
        ▼
 ┌──────────────┐    Rewrite rules (from equations/rewrites in the grammar)
 │ Saturation    │    are applied iteratively. Each rule match adds new
 │ Loop          │    e-nodes and merges classes. Rebuild restores the
 │               │    congruence invariant after each iteration.
 │ match ->      │
 │ apply ->      │
 │ rebuild ->    │
 │ check         │
 └──────┬───────┘
        │
        ▼
 ┌──────────────┐    The extraction pass traverses the e-graph bottom-up,
 │ EClass ->     │    selecting the minimum-cost e-node from each class
 │ extract()     │    according to the chosen cost function. The result
 │               │    is a concrete term in the original term algebra.
 └──────┬───────┘
        │
        ▼
 Optimized Term (smallest / shallowest / cheapest equivalent)
```

### Invariants Maintained Throughout

1. **Congruence**: if `find(a) == find(b)` then for every e-node
   `f(... a ...)` there exists a congruent e-node `f(... b ...)` in the
   same class.

2. **Hashcons uniqueness**: no two e-nodes with the same canonical children
   coexist in the hashcons table. Rebuild enforces this after merges.

3. **Parent tracking**: each e-class maintains a list of parent e-nodes
   that reference it as a child, enabling bottom-up congruence propagation.

---

## Integration with Confluence Analysis

The e-graph provides a direct computational mechanism for answering the
joinability question that drives confluence analysis (T01/T02). Given a critical
pair (s, t) arising from overlapping rewrite rules:

1. **Insert** both terms s and t into the e-graph.
2. **Saturate** using the grammar's rewrite rules.
3. **Query**: if `find(s) == find(t)` after saturation, the pair is joinable
   and T01 is suppressed. The e-graph provides a concrete **joinability witness**
   (EG04) by extracting the common reduct from the shared e-class.

This approach is strictly more powerful than bounded rewriting for joinability
checking: the e-graph simultaneously explores all possible rewriting sequences
up to the resource limit, whereas sequential rewriting commits to a single
sequence and may miss the joining path.

### Interaction Matrix

| Analysis         | E-Graph Role                                      | Diagnostic   |
|------------------|---------------------------------------------------|--------------|
| Confluence (T01) | Joinability check via class membership             | EG04         |
| Confluence (T02) | Strengthens confidence (all pairs joined)          | --           |
| Guard simplify   | Rewrite guards to simpler equivalent forms         | EG02         |
| Dead code        | Discover equivalences that make branches redundant | EG01         |
| Cost-benefit     | Gate: `EgraphSaturation` with configurable budget  | --           |

### Critical Pair Workflow

```
 T01 fires: critical pair (s, t) non-joinable
        │
        ▼
 E-graph inserts s, t
        │
        ▼
 Saturation (bounded by max_nodes / max_iterations)
        │
        ├── find(s) == find(t)?
        │       │
        │       ├── Yes: EG04 fires (joinability witness found)
        │       │         T01 downgraded or suppressed
        │       │
        │       └── No: T01 stands, pair genuinely non-joinable
        │                within the analysis budget
        │
        └── Saturation did not converge?
                │
                └── EG03 fires (resource limit reached)
```

---

## Cost Function Catalog

E-graph extraction selects the minimum-cost representative from each e-class.
Three built-in cost functions are provided, with a trait for user extension.

### AstSize

Counts the total number of e-nodes in the extracted term tree. This is the
default cost function and produces the smallest equivalent term.

```
cost(leaf) = 1
cost(f(c_1, ..., c_n)) = 1 + sum(cost(c_i))
```

**Use case**: general-purpose simplification, minimizing generated code size,
reducing AST node count for hash-consing efficiency.

### AstDepth

Returns the maximum nesting depth of the extracted term. Prefers wide, shallow
terms over deep, narrow ones.

```
cost(leaf) = 1
cost(f(c_1, ..., c_n)) = 1 + max(cost(c_i))
```

**Use case**: reducing stack depth in recursive evaluation, minimizing
trampoline frame depth in PraTTaIL's stack-safe parser, bounding recursion
depth for verification analyses.

### WeightedCost

Associates a per-constructor weight (from cost-benefit analysis or user
annotation) and sums them. Weights can reflect runtime cost (e.g., allocation
frequency), codegen cost (e.g., instruction count), or domain-specific
priorities.

```
cost(leaf) = weight(leaf)
cost(f(c_1, ..., c_n)) = weight(f) + sum(cost(c_i))
```

**Use case**: codegen optimization (prefer cheaper constructors), runtime
performance (prefer constructors that avoid allocation), domain-specific
optimization (prefer normal forms with semantic significance).

### Custom Cost Functions

The `CostFunction` trait can be implemented by users for domain-specific
extraction strategies:

```rust
trait CostFunction {
    type Cost: Ord + Clone;
    fn cost(&self, enode: &ENode, children: &[Self::Cost]) -> Self::Cost;
}
```

---

## Configuration Tuning

### Parameter Defaults

| Parameter        | Default | Description                                          | Tuning Guidance                              |
|------------------|---------|------------------------------------------------------|----------------------------------------------|
| `max_nodes`      | 10,000  | Maximum e-nodes before saturation aborts             | Increase for complex grammars; decrease for faster compile |
| `max_iterations` | 30      | Maximum saturation iterations                        | Increase if EG03 fires frequently            |
| `cost_function`  | AstSize | Extraction cost function                             | AstDepth for stack-depth minimization        |
| `node_limit`     | 5,000   | Soft limit triggering compaction heuristics           | Lower for memory-constrained environments    |
| `time_limit_ms`  | 1,000   | Wall-clock timeout for saturation phase               | Increase for one-shot offline compilation    |
| `batch_size`     | 1,000   | E-nodes added per iteration before rebuild            | Higher reduces rebuild overhead, more memory |

### Environment Variable Overrides

| Variable                      | Format   | Example                   |
|-------------------------------|----------|---------------------------|
| `PRATTAIL_EGRAPH_MAX_NODES`   | integer  | `PRATTAIL_EGRAPH_MAX_NODES=50000` |
| `PRATTAIL_EGRAPH_MAX_ITER`    | integer  | `PRATTAIL_EGRAPH_MAX_ITER=100`    |
| `PRATTAIL_EGRAPH_COST`        | string   | `PRATTAIL_EGRAPH_COST=depth`      |
| `PRATTAIL_EGRAPH_TIME_LIMIT`  | integer (ms) | `PRATTAIL_EGRAPH_TIME_LIMIT=5000` |

### Tuning Heuristics

1. **Small grammars (< 50 rules)**: defaults are sufficient. Saturation
   typically completes in 3--8 iterations with < 2,000 e-nodes.

2. **Medium grammars (50--200 rules)**: consider `max_nodes = 25,000` and
   `max_iterations = 50`. Monitor EG03 frequency; if it fires on > 10% of
   critical pairs, increase limits.

3. **Large grammars (> 200 rules)**: set `time_limit_ms = 3000` and
   `max_nodes = 50,000`. Enable batch compaction (`node_limit = 10,000`).
   Consider disabling the e-graph for non-critical analyses via cost-benefit
   gating.

4. **CI/CD pipelines**: use conservative defaults to avoid compile-time
   regressions. Set `PRATTAIL_EGRAPH_TIME_LIMIT=500` for fast feedback.

---

## Performance Characteristics

| Operation               | Time Complexity           | Space Complexity       | Notes                                     |
|-------------------------|---------------------------|------------------------|--------------------------------------------|
| `add(enode)`            | O(alpha(n)) amortized     | O(1) per node          | Union-find with path compression           |
| `union(a, b)`           | O(alpha(n)) amortized     | O(1) amortized         | Union by rank                              |
| `find(id)`              | O(alpha(n)) amortized     | O(1)                   | Path compression                           |
| `rebuild()`             | O(m * alpha(n))           | O(m)                   | m = number of dirty e-nodes               |
| `match_pattern(lhs)`    | O(|E| * |lhs|)            | O(|matches| * |vars|)  | Relational e-matching                      |
| `saturate(rules, N)`    | O(N * |R| * |E| * |lhs|)  | O(|E|)                 | N iterations, |R| rules                    |
| `extract(class, cost)`  | O(|E|)                    | O(|classes|)           | Bottom-up dynamic programming              |
| `is_equivalent(s, t)`   | O(alpha(n))               | O(1)                   | After saturation, just a `find` comparison |

Where:
- n = number of e-classes
- m = number of e-nodes modified since last rebuild
- |E| = total number of e-nodes in the e-graph
- |R| = number of rewrite rules
- |lhs| = average size of rule left-hand-side patterns
- alpha = inverse Ackermann function (effectively constant)

### Memory Profile

| Component        | Per-Unit Cost       | Typical Total (1K rules) |
|------------------|---------------------|--------------------------|
| E-node           | 40--64 bytes        | 400 KB -- 640 KB         |
| E-class          | 80--120 bytes       | 80 KB -- 120 KB          |
| Hashcons entry   | 24--32 bytes        | 240 KB -- 320 KB         |
| Union-find       | 8 bytes per class   | 8 KB                     |
| Match results    | 16 bytes per subst  | Variable (< 1 MB typ.)   |
| **Total**        |                     | **< 2 MB typical**       |

---

## Compile-Time vs Runtime Classification

The e-graph equality saturation analysis in PraTTaIL is strictly a
**compile-time** analysis. It operates during the `Generate` phase of the
`language!` macro expansion, alongside other mathematical analyses (TRS,
VPA, WPDS, etc.).

| Aspect              | Classification | Rationale                                         |
|----------------------|----------------|---------------------------------------------------|
| E-graph construction | Compile-time   | Built from grammar equations/rewrites             |
| Saturation loop      | Compile-time   | Runs during macro expansion                       |
| Equivalence queries  | Compile-time   | Used by lint and confluence analysis              |
| Extraction           | Compile-time   | Produces optimized term forms for codegen         |
| Cost functions       | Compile-time   | Guide extraction during code generation           |
| EG01--EG04 lints     | Compile-time   | Emitted as part of `run_lints()`                  |
| Generated code       | Runtime        | May use e-graph-discovered equivalences as rewrites |

The e-graph is not present in generated parser code. Its results are consumed
by the code generator to:

1. **Simplify guards**: replace complex guard expressions with equivalent
   simpler forms discovered during saturation (EG02).

2. **Eliminate redundant branches**: when saturation discovers that two
   constructors are equivalent, one branch can be eliminated or merged.

3. **Strengthen confluence results**: joinability witnesses (EG04) allow T01
   to be suppressed or downgraded, producing cleaner diagnostic output.

4. **Inform cost-benefit gating**: saturation statistics feed into the
   cost-benefit analyzer to decide whether downstream analyses are worth
   running on a grammar of the observed complexity.

---

## Algorithm Detail: Rebuild with Congruence Restoration

The rebuild phase is the most subtle part of the e-graph implementation.
After a batch of `union()` operations, the congruence invariant may be
violated: two e-nodes that are now congruent (same function symbol,
pairwise-equivalent children) may reside in different e-classes.

Rebuild proceeds as follows:

```
rebuild():
    while worklist is not empty:
        enode = worklist.pop()
        canonical = canonicalize(enode)       // replace children with find()
        if hashcons[canonical] exists:
            existing_class = hashcons[canonical]
            merge(enode.class, existing_class)  // may add more to worklist
        else:
            hashcons.remove(enode)              // remove old (non-canonical) entry
            hashcons[canonical] = enode.class   // insert canonical entry
```

The key properties of this algorithm:

- **Idempotent**: running rebuild twice with no intervening merges is a no-op.
- **Monotone**: rebuild only merges classes, never splits them.
- **Bounded**: each e-node is processed at most once per rebuild call (the
  worklist is drained and not re-populated unless new merges occur).

---

## Integration Points with PraTTaIL Pipeline

### Pipeline Position

```
 ┌──────────┐   ┌──────────┐   ┌──────────────┐   ┌──────────┐   ┌──────────┐
 │ Parse    │──>│ Validate │──>│ Predict/WFST │──>│ Analysis │──>│ Codegen  │
 │ AST      │   │ Grammar  │   │ Dispatch     │   │ Phase    │   │          │
 └──────────┘   └──────────┘   └──────────────┘   └─────┬────┘   └──────────┘
                                                        │
                                                        ▼
                                      ┌─────────────────────────────────┐
                                      │ Mathematical Analysis Pipeline  │
                                      │                                 │
                                      │  ┌────────────┐                 │
                                      │  │ TRS (T01-4)│                 │
                                      │  └─────┬──────┘                 │
                                      │        │                        │
                                      │  ┌─────▼──────┐                 │
                                      │  │ E-Graph    │  <-- NEW        │
                                      │  │ (EG01-04)  │                 │
                                      │  └─────┬──────┘                 │
                                      │        │                        │
                                      │  ┌─────▼──────┐                 │
                                      │  │ Other      │                 │
                                      │  │ analyses   │                 │
                                      │  └────────────┘                 │
                                      └─────────────────────────────────┘
```

### Cost-Benefit Gating

The e-graph analysis is gated by a `EgraphSaturation` variant in the
cost-benefit analyzer. The gate evaluates:

- **Grammar complexity**: number of equations and rewrite rules. Grammars with
  fewer than 2 equations skip e-graph analysis entirely (no benefit).
- **Critical pair count**: if TRS analysis found zero critical pairs, the
  e-graph's joinability contribution is zero and it can be skipped.
- **Prior saturation history**: if a previous compilation of the same grammar
  saturated quickly (< 5 iterations), the gate allows the analysis. If it hit
  max_iterations, the gate may recommend increasing limits or disabling.

---

## References

1. Willsey, M., Nandi, C., Wang, Y. R., Flatt, O., Tatlock, Z., & Panchekha, P.
   (2021). *egg: Fast and Extensible Equality Saturation*. Proceedings of the
   ACM on Programming Languages, 5(POPL), 1--29.
   https://doi.org/10.1145/3434304

2. Tate, R., Stepp, M., Tatlock, Z., & Lerner, S. (2009). *Equality
   Saturation: A New Approach to Optimization*. Proceedings of the 36th Annual
   ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages (POPL),
   264--276. https://doi.org/10.1145/1480881.1480915

3. Nelson, G., & Oppen, D. C. (1980). *Fast Decision Procedures Based on
   Congruence Closure*. Journal of the ACM, 27(2), 356--364.
   https://doi.org/10.1145/322186.322198

4. Knuth, D. E., & Bendix, P. B. (1970). *Simple Word Problems in Universal
   Algebras*. In Computational Problems in Abstract Algebra, 263--297.
   Pergamon Press.

5. Baader, F., & Nipkow, T. (1998). *Term Rewriting and All That*. Cambridge
   University Press. ISBN 978-0-521-77920-3.

6. Downey, P. J., Sethi, R., & Tarjan, R. E. (1980). *Variations on the
   Common Subexpression Problem*. Journal of the ACM, 27(4), 758--771.
   https://doi.org/10.1145/322217.322228

7. De Moura, L., & Bjorner, N. (2007). *Efficient E-Matching for SMT
   Solvers*. In Automated Deduction -- CADE-21, LNCS 4603, 183--198.
   Springer. https://doi.org/10.1007/978-3-540-73595-3_13
