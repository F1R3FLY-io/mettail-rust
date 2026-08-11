# Stack-Safe Term-Depth Measurement

## Purpose

The depth generator emits a `term_depth()` method for every generated MeTTaIL
term category. The method measures host-term nesting; it does not reject deep
terms, truncate traversal, or make a partial result appear complete. Generated
Dovetail reports use the value when deriving a saturation-work allowance, and
they return an explicit error if saturation does not converge within that
allowance.

The historical `ART05 DepthBound` cost-benefit recommendation was removed in
2026-08-10. It proposed an artificial accepted-term cutoff and was never a
production transformation in the Dovetail/Rho generator.

**Implementation:** `macros/src/gen/term_ops/depth.rs`

## Depth semantics

| Term shape | Contribution |
|---|---:|
| Variable, scalar literal, nullary constructor | 0 |
| Constructor application | one level plus the maximum child depth |
| Collection category | one level plus the maximum element depth |
| Collection field inside a constructor | maximum element depth; the field container adds no level |
| Binder or multi-binder | one level plus the maximum pre-scope-field/body depth |
| Predicate or opaque capture | 0; it is not a host sub-term |

Empty collection categories therefore have depth one. An empty collection
field contributes zero below its enclosing constructor.

## Iterative pushdown traversal

Before stack-safety item #162, generated methods called `term_depth()`
recursively on every child. The replacement is a heap-backed pushdown
automaton whose work item is `(node, distance-from-root)`. It maintains one
running maximum and therefore needs neither a result stack nor post-order
combine frames.

Let `base(node)` be zero for leaf kinds and one for other host-term nodes. The
measured depth is:

```math
\operatorname{depth}(n)
=
\max_{m \in \operatorname{desc}(n)}
\left(\operatorname{distance}(n,m)+\operatorname{base}(m)\right).
```

For a non-leaf node, every child is one edge farther from the root. Taking the
maximum over the descendants of each child therefore reproduces the recursive
equation “one plus maximum child depth.” For a leaf, the root contribution is
zero. For a non-leaf without pushed children—such as an empty collection—the
root contribution is one. These cases establish the recurrence without a
post-order result stack.

### Literate pseudocode

```text
procedure TERM_DEPTH(root):
    work := pooled vector containing (root, 0)
    deepest := 0

    while work is not empty:
        (node, distance) := work.pop()
        deepest := max(deepest, distance + base(node))

        child_distance := distance + 1
        for each host-subterm child position of node:
            work.push((child, child_distance))

    return deepest
```

Collection traversal delegates to the shared collection-walk planner with an
order-agnostic policy because `max` is commutative. This covers vectors, sets,
bags, maps, and PathMaps. Map keys and values are both visited; bag
multiplicities are counts rather than term children.

## Generated architecture

```text
generate_term_depth_methods
├── generate DepthTask variants: one pointer-and-distance variant per category
├── generate one category handler per category
├── generate depth_iterative worklist driver
└── generate term_depth wrappers
    ├── take a thread-local pooled Vec<DepthTask>
    ├── seed the root at distance zero
    ├── drain the worklist
    └── clear and return the allocation to the pool
```

Raw pointers in `DepthTask` are derived from the caller's immutable `&self` and
are dereferenced only while that borrow remains live on the same thread. The
thread-local pool supports re-entrancy: a nested call observes an empty slot,
uses its own vector, and returns that vector independently.

## Complexity

For `n` visited host-term nodes and maximum explicit frontier size `w`:

- time is linear in `n`;
- native call-stack use is constant with respect to nesting depth;
- worklist storage is proportional to `w` and is reused after the first call;
- no secondary value stack is allocated.

The implementation uses saturating distance addition so an input exceeding
`u32::MAX` nesting cannot wrap to a smaller measurement.

## Verification evidence

The generated traversal is covered by:

- exact closed-form depth laws for alternating and collection-rich generated terms;
- differential checks for vectors, sets, bags, maps, PathMaps, binders, and opaque leaves;
- a 20,000-level traversal on a 256 KiB native stack;
- the generated traversal-boundary census, which classifies `ast_term_depth` as flat;
- full PraTTaIL and generated-language regression suites.

The public result semantics are unchanged from the recursive oracle; only the
evaluation strategy and allocation reuse changed.
