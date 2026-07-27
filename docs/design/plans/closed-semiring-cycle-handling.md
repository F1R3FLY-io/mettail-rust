# Closed-Semiring Cycle Handling — Phase C-bis Design

**Date**: 2026-05-17 (amended 2026-05-17 for Newton's method)
**Branch**: `feature/wfst-architecture`
**Status**: design ready for user review (NO code modifications until approved)
**Origin**: Opedal et al. (ACL 2023) §6 + App E; Lehmann (1977); per
`~/.claude/plans/earley-vs-sppf-comparison.md`
**Amendment**: replaces Lehmann's matrix-star with Newton's method per
`~/.claude/plans/multi-call-scc-linearization.md` — fully principled
solution for multi-call SCC packings (>1 in-SCC child). Degrades to
1-iteration Lehmann (zero overhead) when no packing is multi-call.

---

## Table of Contents

1. [Glossary of Terms](#1-glossary-of-terms)
2. [Background — Why Cycles Matter in SPPFs](#2-background--why-cycles-matter-in-sppfs)
3. [The Problem the Paper Solves](#3-the-problem-the-paper-solves)
4. [Mapping the Paper's Technique onto Our SPPF](#4-mapping-the-papers-technique-onto-our-sppf)
5. [Why Lehmann Alone Is Insufficient (Multi-Call SCC)](#5-why-lehmann-alone-is-insufficient-multi-call-scc)
6. [Newton's Method on ω-Continuous Semirings](#6-newtons-method-on--continuous-semirings)
7. [Five-Step Implementation](#7-five-step-implementation)
8. [New Trait Requirements](#8-new-trait-requirements)
9. [Worked Examples](#9-worked-examples)
10. [Test Plan](#10-test-plan)
11. [Migration Strategy](#11-migration-strategy)
12. [LoC Estimate](#12-loc-estimate)
13. [Mandate Compliance](#13-mandate-compliance)
14. [Trade-offs (Honest Accounting)](#14-trade-offs-honest-accounting)
15. [Interactions with Other Phases](#15-interactions-with-other-phases)
16. [Risk Register](#16-risk-register)
17. [Performance Analysis](#17-performance-analysis)
18. [Numerical Stability for Floating-Point Semirings](#18-numerical-stability-for-floating-point-semirings)
19. [References](#19-references)
20. [Critical Files for Implementation](#20-critical-files-for-implementation)

---

## 1. Glossary of Terms

| Term | Definition |
|------|------------|
| **Semiring `<W, ⊕, ⊗, 0, 1>`** | Algebraic structure with two operations: `⊕` (commutative monoid with identity 0) and `⊗` (monoid with identity 1, distributes over `⊕`, 0 annihilates). |
| **Idempotent semiring** | A semiring where `a ⊕ a = a` for all `a`. Examples: Boolean (OR/AND), Tropical (min/+), Lexicographic. Cycle-skip is sound here. |
| **Closed semiring** | A semiring equipped with a Kleene star operator `*` such that `a* = 1 ⊕ a ⊕ a² ⊕ ...` is well-defined (infinite sums converge). |
| **ω-continuous semiring** | A closed semiring where countable suprema exist and `⊕` is ω-continuous. Required for Newton's method to converge to least fixpoint. |
| **Star operator (`star(a)` or `a*`)** | Sum of infinite geometric series `1 ⊕ a ⊕ a² ⊕ ...`. For probabilities in [0,1): `1/(1-a)`. For Boolean: `true`. For Tropical with `a ≥ 0`: `0` (the additive identity in min-plus is +∞, but min(0, a, 2a, ...) = 0 when a ≥ 0). |
| **SPPF (Shared Packed Parse Forest)** | Tomita 1986 / Scott-Johnstone 2010 data structure that compactly represents all derivations of an ambiguous parse. Used by PraTTaIL since Phase C. |
| **Symbol node** | An SPPF node representing a nonterminal occurrence identified by `(nt_tag, lo_pos, hi_pos)`. Multiple Packings can attach to the same Symbol (ambiguity). |
| **Packing node** | An SPPF node representing one specific derivation choice for some parent Symbol. Carries `rule_idx`, `children` (ordered Vec of child SppfIds), and `weight: W`. |
| **SCC (Strongly Connected Component)** | A maximal subset of nodes in a directed graph where every node reaches every other node. In our SPPF, SCCs arise when Symbol-dedup makes recursive Symbols share the same SppfId. |
| **Trivial SCC** | A single-node SCC with no self-loop. The common case — most Symbols are in trivial SCCs. |
| **Non-trivial SCC** | A multi-node SCC, OR a single-node SCC with a self-loop edge. These are where matrix-star / Newton matters. |
| **Multi-call packing** | A packing whose `children` contains MORE THAN ONE Symbol from the same SCC as the packing's parent Symbol. Examples: `S → S "+" S` (left/right are both `S`-nodes from the same SCC). |
| **Inside weight** | Goodman's term for `Y_X = ⊕_{X → α} c(X→α) ⊗ Π Y_{rhs(r)}` — the total semiring weight of all derivations rooted at nonterminal `X`. |
| **Outside weight** | Goodman's term for the dual: total weight of all derivations CONTEXT-AROUND `X`. Used in inside-outside EM. Not needed for our current realize use case. |
| **Lehmann's algorithm (1977)** | Iterative `O(n³)` solver for `A* = (I⊕A)*` in closed semirings. Generalization of Floyd-Warshall. Solves LINEAR systems `Y = AY ⊕ b`. |
| **Newton's method on ω-continuous semirings (Esparza 2007)** | Generalization of Newton-Raphson to NON-linear polynomial fixpoint systems `Y = f(Y)` over closed semirings. Each iteration solves a linear system via Lehmann. |
| **Multi-variable Leibniz rule** | The chain rule for the formal differential of a polynomial: `∂(Y_1 ⊗ Y_2 ⊗ Y_3)/∂Y_2 = Y_1 ⊗ Y_3`. Used to compute the Jacobian (differential matrix) at each Newton iterate. |
| **Realize** | The post-parse process of materializing AST values from an SPPF by invoking each Packing's `action_fn`. Implemented in `wpda_walker.rs::realize_root_to_terms_with_weights`. |
| **Cycle-skip** | The current implementation's behavior at cycle back-edges: discard the cyclic packing's contribution. Sound only under idempotent ⊕. |
| **Tri-color DFS** | Classic 3-state DFS (WHITE/GRAY/BLACK) used for cycle detection. Current implementation uses this; we'll replace with Tarjan SCC for the new approach. |
| **Tarjan's SCC algorithm** | Linear-time O(V+E) algorithm for finding all SCCs of a directed graph. Iterative variant in `buchi.rs:798-851`. |

---

## 2. Background — Why Cycles Matter in SPPFs

### How SPPF cycles arise

In Scott-Johnstone packed SPPFs, Symbol nodes are **deduplicated by
`(nt_tag, lo_pos, hi_pos)`**. This means two different cursor reductions
of the same nonterminal at the same input span share a single SppfId.

This creates cycles in two grammar shapes:

**Direct left/right recursion**:
```text
S → S "+" S | num
parsing "1 + 2 + 3":
  S_{0,7} ─[+_R]→ Packing → S_{0,3}, "+", S_{4,7}
                          ↘ S_{0,3} ─[+_L]→ Packing → S_{0,1}, "+", S_{2,3}
                                                      ↑ same span shape as outer
  (Symbol-dedup makes S_{0,3} share an SppfId; the cyclic structure
   exists when the recursive shape is realized.)
```

**Unit / unary cycles** (less common):
```text
S → A | num
A → S
A → S forms S → A → S, a unit cycle.
```

**Mutual recursion**:
```text
A → B + 1
B → A + 1
```

### Why this matters for weight aggregation

In Goodman's semiring parsing framework, every Symbol `X` has an
**inside weight**:
```text
Y_X = ⊕_{rules X → α} c(X → α) ⊗ Π_{y ∈ α} Y_y
```
(For each production, multiply its weight by the product of its
children's inside weights, then sum over all productions.)

When `Y_X` appears on both sides of this equation (because some `Y_y`
on the RHS resolves back to `Y_X` through the SCC), the equation
becomes a fixpoint problem: `Y_X = f(Y_X)`. Under arbitrary semirings,
this fixpoint has no closed form computable by simple recursion — it
needs proper fixpoint machinery.

### Why the current code "works"

PraTTaIL's production semiring is `LexicographicWeight`, which is
**idempotent tropical** (`min`-style). For idempotent ⊕, the
geometric series collapses:
```text
A* = I ⊕ A ⊕ A² ⊕ ... = I (under idempotency, where A ⊆ I or A ≤ I)
```
Concretely, `a ⊕ a ⊕ a ⊕ ... = a`. So skipping the cyclic packing
entirely gives the SAME numerical answer as integrating it infinitely
many times — *under idempotency only*. The current `cycle-skip + RealizeColor::Gray`
strategy at `wpda_walker.rs:3348` is correct *because* of this
idempotency.

The moment we switch to a non-idempotent semiring (LogWeight,
CountingWeight, EntropyWeight), skip-vs-integrate gives DIFFERENT
numerical results, and skip is WRONG.

---

## 3. The Problem the Paper Solves

Opedal et al. (ACL 2023) §6 + App E provide the rigorous solution
for semiring-weighted parsing under arbitrary closed semirings,
including non-idempotent ones.

### The chart-parsing context (paper's setup)

In an Earley chart, each item `[A, i, j]` carries an inside weight
`β̂[A, i, j]`. The recurrence relates items via the deduction rules
(SCAN, COMPLETE, PREDICT). When the grammar has unit/unary cycles,
the recurrence becomes:
```text
β̂[A] = ⊕_{A → B} c(A → B) ⊗ β̂[B]   (unit production)
β̂[B] = ⊕_{B → A} c(B → A) ⊗ β̂[A]   (unit production)
```
This is a linear fixpoint system. The paper formalizes it as:
```text
Y = AY ⊕ b
```
where:
- `Y[i]` is the inside weight of nonterminal `i`.
- `A[i,j]` is the per-production weight of `i → j` (unit productions
  only, in the canonical case).
- `b[i]` is the sum of "exit weights" — contributions from productions
  whose RHS contains no in-SCC nonterminals.

### Solution: `Y = A* ⊗ b`

The paper invokes Kleene's identity: the solution to `Y = AY ⊕ b` in
a closed semiring is `Y = A* ⊗ b`, where `A* = (I ⊕ A)* = I ⊕ A ⊕ A² ⊕ ...`.

`A*` is computed via **Lehmann's algorithm (1977)**, the closed-semiring
analogue of Floyd-Warshall:
```text
function lehmann_matrix_star(A):
    for k = 1..n:                                    # pivot vertex
        k_star = star(A[k][k])                       # self-loop closure
        for i = 1..n:
            for j = 1..n:
                A[i][j] ← A[i][j] ⊕ A[i][k] ⊗ k_star ⊗ A[k][j]
    return A
```
The algorithm runs in `O(n³)` time and `O(n²)` space. After it
completes, `A[i][j]` contains the closed sum of all paths from
vertex `i` to vertex `j` (including paths that loop arbitrarily
many times through any vertex).

---

## 4. Mapping the Paper's Technique onto Our SPPF

The paper's `(A, b)` are derived from the GRAMMAR; our `(A, b)` are
derived from the SPPF (a runtime data structure built per-parse). The
underlying algebra is identical; the data sources differ.

### Symbol nodes are nonterminal occurrences

In our SPPF, a Symbol node `S_{nt,lo,hi}` plays the role of
nonterminal `A` in the paper's `Y[A]`. The inside weight at this
Symbol is what we want to compute (and currently approximate via
cycle-skip).

### Packings are productions

A Packing `P ∈ packings_of(S_i)` with `children = [c_1, c_2, ..., c_m]`
plays the role of a single production rewriting `S_i`. The packing's
`weight: W` (set per `Phase C.3`) is the per-production constant
`c(S_i → child_pattern)`.

### The A matrix and b vector

For an SCC `S = [s_0, s_1, ..., s_{k-1}]` of Symbol nodes:

**A[i,j]** = sum over all packings `P ∈ packings_of(s_i)` where exactly
one child of `P` is the in-SCC Symbol `s_j` (and all other children
are outside the SCC):
```text
A[i,j] = ⊕_{P: P.children contains s_j ∈ SCC, others outside}
            (P.weight ⊗ Π_{c ∈ P.children, c ≠ s_j} memo[c].weight_sum)
```

**b[i]** = sum over all "exit packings" of `s_i` — packings whose
children are ALL outside the SCC:
```text
b[i] = ⊕_{P: all P.children outside SCC}
            (P.weight ⊗ Π_{c ∈ P.children} memo[c].weight_sum)
```

**Cyclic weight at `s_i`**: `Y[i] = (A* ⊗ b)[i]`. This replaces the
current `weight_sum` at cyclic Symbols.

### What stays the same

- The Phase C `Sppf<W>` data structure: unchanged.
- Symbol-dedup: unchanged (we ONLY consume what's already there).
- `Packing.weight` and `Symbol.weight_sum` fields: unchanged (the
  link-time aggregation in `link_packing_to_symbol` still runs).
- The realize path's CARTESIAN PRODUCT over Packing children: unchanged.
- The realize entry point's external signature: unchanged.

What changes: how `Symbol.weight_sum` is *computed at realize time*
when the Symbol is in a non-trivial SCC. Currently: tri-color skip.
New: matrix-star (or Newton if multi-call) `(I⊕A)* ⊗ b`.

---

## 5. Why Lehmann Alone Is Insufficient (Multi-Call SCC)

### The multi-call problem

The paper's recurrence assumes linearity:
```text
Y = AY ⊕ b
```
This holds when every production rewriting `S_i` references AT MOST ONE
in-SCC Symbol. For unit productions (`S → A`) and most natural
recursive shapes, this is fine.

But many real grammar productions reference MORE THAN ONE in-SCC
Symbol. The canonical example is the binary operator:
```text
S → S "+" S
```
Both `S` references on the RHS are in the same SCC as the outer `S`.
The recurrence becomes:
```text
Y_S = c(S → S+S) ⊗ Y_S ⊗ Y_S ⊕ c(S → num) ⊗ Y_num
```
This is **bilinear in Y_S** — not a linear equation. Lehmann's
algorithm solves linear systems only; it cannot directly solve this.

### Why this matters for PraTTaIL

Auditing production grammars (full enumeration):

| Grammar | Multi-call packing examples |
|---------|----------------------------|
| `calculator.rs` | `Or`, `And`, `Plus`, `Times`, `BitOr`, `BitAnd`, `BitXor`, `Mul`, `Div`, `Mod`, `Pow` |
| `ambient.rs`    | `PPar` (variadic), `PNew` (binder + body both Proc) |
| `rholang.rs`    | Dozens of `a:Proc, b:Proc → Proc` rules |
| `ledtest.rs`    | `Plus`, `Times`, `Pow` |
| `class2multi.rs`, `class3multi.rs` | Multiple collection-bearing constructors |

The SCC containing `Proc` (or whatever the primary recursive
nonterminal is) ALWAYS has multi-call packings — they're the natural
shape of binary operators.

### The naive stopgap and its bug

The original (pre-amendment) plan handled this by distributing
`outside_product` into each of the multi-call slots:
```rust
_ => {
    // Multi-call: P references >1 SCC-internal Symbol.
    for &j in &in_scc_targets {
        a[i][j] = a[i][j].plus_ref(&outside_product);   // BUG: double-counts
    }
}
```

This is WRONG. The multi-call contribution is `outside_product ⊗ Y_j ⊗ Y_k`
(a PRODUCT), not `outside_product ⊗ Y_j ⊕ outside_product ⊗ Y_k`
(a SUM). Under idempotent `⊕`, the sum happens to be a pessimistic
upper bound on the true product. Under non-idempotent semirings, it's
just plain wrong.

This violates Mandate P3 (semiring `⊕` at merge): what we're summing
into the matrix is not a true alternative — it's a missing product.

---

## 6. Newton's Method on ω-Continuous Semirings

### The breakthrough (Esparza-Kiefer-Luttenberger 2007)

Esparza, Kiefer, and Luttenberger generalized Newton-Raphson to
ω-continuous semirings. Their key insight: at iterate `Y^{(n)}`, the
non-linear fixpoint `Y = f(Y)` can be locally linearized via the
formal differential `Df(Y)` (the Jacobian in semiring terms). The
linearized system `δ = Df(Y^{(n)}) · δ ⊕ (f(Y^{(n)}) ⊖ Y^{(n)})` is
solvable by Lehmann. The update `Y^{(n+1)} = Y^{(n)} ⊕ δ` is
monotone — each iterate is `⊒` the previous one.

For our case, where `⊖` doesn't exist in semirings, the equivalent
formulation is:
```text
Y^{(n+1)} = Df*(Y^{(n)}) ⊗ f(Y^{(n)})
```
where `Df*` is the Kleene-closed differential matrix.

### The multi-variable Leibniz rule

For a polynomial production `f_i(Y) = outside_product ⊗ Π_{l=1..m} Y_{c_l}`,
the partial derivative with respect to `Y_{c_k}` is (by the
multi-variable Leibniz rule):
```text
∂f_i/∂Y_{c_k} = outside_product ⊗ Π_{l < k} Y^{(n)}_{c_l} ⊗ Π_{l > k} Y^{(n)}_{c_l}
```
i.e., the product of "everything except position k", with `Y` evaluated
at the current iterate.

For our SPPF, this means: at each Newton iteration, the differential
matrix `Df(Y^{(n)})[i][j]` is the sum over all packings of `s_i` that
reference `s_j` (possibly multiple times) of the product of all other
in-SCC children at their current iterate values, times the outside
product.

### Convergence

For monotone polynomial systems over ω-continuous semirings:

| Semiring | Convergence rate |
|----------|------------------|
| Idempotent + bounded (Boolean, Tropical, Lexicographic, Arctic) | **In ≤ |SCC| iterations** (Esparza Thm 5.1) |
| `CountingWeight` (with saturation at u64::MAX) | **1 iteration** (saturates immediately on cycles) |
| `LogWeight`, `EntropyWeight` (probability) | **Geometric** — cap at `max_iters = 64` |

### Linear fast-path

When NO packing in the SCC is multi-call, the differential `Df(Y)`
is constant in `Y` (no `Y` factors appear in the partial derivatives —
the only "in-SCC child" is the variable itself). The first Newton
iteration reproduces `Y = A* ⊗ b` exactly. The implementation detects
this and short-circuits.

**Net effect**: Newton is a strict superset of single-shot Lehmann.
Same speed on the unary/transitive case; correctly handles multi-call.

---

## 7. Five-Step Implementation

### Step 1 — Tarjan SCC over Symbol-induced subgraph (~80 LoC, `sppf.rs`)

```rust
/// Returns the strongly-connected components of the Symbol-induced
/// subgraph reachable from `root`.
///
/// **Vertices**: every `SppfNode::Symbol` reachable from `root`.
/// **Edges**: `S_i → S_j` iff some `Packing ∈ packings_of(S_i)` has
/// `S_j` (a Symbol) among `children`. Packings, Terminals, Epsilons,
/// CollectionIds, Predicates, BinderScopes are transparent
/// edge-bearers — they don't appear as vertices.
///
/// **Why Symbol-only**: SPPF cycles always traverse at least one
/// Symbol (they arise from `(nt, lo, hi)` dedup collisions, which
/// only Symbols experience). Non-Symbol nodes are inherently acyclic
/// (Packings link to children but children never link back to
/// Packings; Terminals are leaves; etc.).
///
/// **Algorithm**: iterative Tarjan (Sedgewick 4ed §4.2.3), to avoid
/// host-stack recursion on deep SPPFs. Reference implementation:
/// `prattail/src/buchi.rs:798-851`.
///
/// **Complexity**: O(V + E) where V = reachable Symbol count, E = sum
/// of packings_of(s).len() over all reachable Symbols.
///
/// **Output**: SCCs in reverse topological order — leaf SCCs first.
/// Each inner Vec is one SCC; singleton Vecs are trivial SCCs.
pub fn tarjan_sccs<W: SemiringRef>(
    sppf: &Sppf<W>,
    root: SppfId,
) -> Vec<Vec<SppfId>>;
```

### Step 2 — SCC-aware DFS dispatch (~50 LoC, `wpda_walker.rs`)

Pre-compute `scc_of: HashMap<SppfId, SccId>` and `scc_meta: Vec<SccMeta<W>>`
at the top of `realize_root_to_terms_with_weights`. Replace the
back-edge GRAY check at line ~3348 with:

```rust
// Pre-compute SCC structure ONCE per realize call (O(V+E)).
let sccs = sppf.tarjan_sccs(root);
let scc_of: FxHashMap<SppfId, SccId> = sccs.iter().enumerate()
    .flat_map(|(scc_id, members)| members.iter().map(move |&s| (s, SccId(scc_id))))
    .collect();
let scc_meta: Vec<SccMeta<W>> = sccs.iter().enumerate().map(|(id, members)| {
    let is_trivial = members.len() == 1
        && !has_self_loop(sppf, members[0], &scc_of);
    SccMeta {
        id: SccId(id),
        symbols: members.clone(),
        local_idx: members.iter().enumerate().map(|(i, &s)| (s, i)).collect(),
        is_trivial,
        solved_weights: OnceCell::new(),  // lazily computed on first use
    }
}).collect();

// Inside the DFS, at Symbol Leave phase:
let scc_id = scc_of[&id];
if scc_meta[scc_id.0].is_trivial {
    // EXISTING tri-color path unchanged.
    process_trivial_symbol(...)
} else {
    // NEW non-trivial SCC path — Newton + matrix-star.
    process_nontrivial_scc_symbol(scc_id, ...)
}
```

### Step 3 — SCC packing factoring (~60 LoC, `sppf.rs`)

```rust
/// Phase C-bis (2026-05-17): factored representation of an SPPF
/// Packing as it contributes to a non-trivial SCC's fixpoint.
///
/// Preserves the full structural decomposition (in-SCC children
/// and outside-product) — does NOT prematurely flatten into a
/// linear A-matrix entry. This is essential for Newton's method
/// to compute the correct multi-variable Leibniz differential
/// for multi-call packings.
pub struct PackingFactored<W> {
    /// SCC-local index of the parent Symbol s_i (this packing
    /// is in packings_of(s_i)).
    pub target_i: usize,
    /// Per-production weight ⊗ Π weight_sums of all children
    /// OUTSIDE the SCC (constant w.r.t. the cyclic unknowns).
    pub outside_product: W,
    /// SCC-local indices of the children INSIDE the SCC,
    /// in source order (order matters for Leibniz: the partial
    /// derivative depends on which factor we differentiate w.r.t.).
    pub in_scc_children: SmallVec<[usize; 4]>,
}

/// Factor a single Packing into its `PackingFactored<W>` form.
pub fn factor_scc_packing<W: SemiringRef>(
    sppf: &Sppf<W>,
    scc: &[SppfId],
    packing_id: SppfId,
    idx: &FxHashMap<SppfId, usize>,         // SppfId → SCC-local index
    memo_outside: &HashMap<SppfId, W>,      // realize results for non-SCC children
) -> PackingFactored<W> {
    let SppfNode::Packing { weight, children, .. } = sppf.node(packing_id).unwrap()
        else { panic!("not a Packing"); };
    // target_i is computed by the caller (it knows which Symbol owns this Packing).
    let mut outside_product = weight.clone();
    let mut in_scc_children = SmallVec::new();
    for &c in children {
        if let Some(SppfNode::Symbol { .. }) = sppf.node(c) {
            if let Some(&j) = idx.get(&c) {
                in_scc_children.push(j);
                continue;
            }
        }
        let w_c = memo_outside.get(&c).cloned().unwrap_or(W::one_ref());
        outside_product = outside_product.times_ref(&w_c);
    }
    PackingFactored {
        target_i: idx[&parent_symbol_of(packing_id)],
        outside_product,
        in_scc_children,
    }
}
```

### Step 4 — Newton's method per SCC (~200 LoC, `semiring.rs`)

```rust
/// Solve `Y = f(Y)` for the inside-weight vector of one SCC, via
/// Newton's method on ω-continuous semirings (Esparza-Kiefer-
/// Luttenberger 2007).
///
/// **Inputs**:
/// - `scc_size`: dimension `k` of the per-SCC weight vector `Y ∈ W^k`.
/// - `packings`: ALL packings whose parent Symbol is in this SCC,
///   factored via `factor_scc_packing`.
/// - `max_iters`: convergence cap for non-idempotent semirings.
///
/// **Behavior**:
/// - **Linear fast-path**: if every packing has `in_scc_children.len() ≤ 1`,
///   build `A` matrix once, run `matrix_star_ref(A)`, return `A* ⊗ b`.
///   This is BYTE-IDENTICAL to the original Lehmann-only plan's
///   single-shot solve. Zero overhead for unary/transitive cycles.
/// - **Newton iteration**: for multi-call packings, iterate
///   `Y^{(n+1)} = Df*(Y^{(n)}) ⊗ f(Y^{(n)})`. Monotonicity guarantees
///   `Y^{(n+1)} ⊒ Y^{(n)}`. Terminate when fixpoint reached or
///   `max_iters` exhausted.
///
/// **Returns**: `Vec<W>` of length `scc_size`, with `Y[i]` the
/// cyclic inside-weight aggregate at the `i`-th Symbol in the SCC.
pub fn solve_scc_weights_newton<W: SemiringRef + StarSemiringRef>(
    scc_size: usize,
    packings: &[PackingFactored<W>],
    max_iters: usize,
) -> Vec<W> {
    // Compute b vector: exit-packing contributions (no in-SCC children).
    let mut b = vec![W::zero_ref(); scc_size];
    for p in packings {
        if p.in_scc_children.is_empty() {
            b[p.target_i] = b[p.target_i].plus_ref(&p.outside_product);
        }
    }

    // Detect linear case.
    let is_linear = packings.iter().all(|p| p.in_scc_children.len() <= 1);

    if is_linear {
        // Build A matrix (constant in Y).
        let mut a = vec![vec![W::zero_ref(); scc_size]; scc_size];
        for p in packings {
            if let Some(&j) = p.in_scc_children.first() {
                a[p.target_i][j] = a[p.target_i][j].plus_ref(&p.outside_product);
            }
        }
        let a_star = matrix_star_ref(&a);
        return (0..scc_size).map(|i| {
            let mut acc = W::zero_ref();
            for j in 0..scc_size {
                acc = acc.plus_ref(&a_star[i][j].times_ref(&b[j]));
            }
            acc
        }).collect();
    }

    // Newton iteration for multi-call SCCs.
    let mut y = vec![W::zero_ref(); scc_size];
    for _iter in 0..max_iters {
        let df = build_differential_matrix(&y, packings, scc_size);
        let df_star = matrix_star_ref(&df);
        let f_y = evaluate_f(&y, packings, &b, scc_size);
        let y_next: Vec<W> = (0..scc_size).map(|i| {
            let mut acc = W::zero_ref();
            for j in 0..scc_size {
                acc = acc.plus_ref(&df_star[i][j].times_ref(&f_y[j]));
            }
            acc
        }).collect();
        if y_next == y {
            return y_next;  // monotone fixpoint reached
        }
        y = y_next;
    }
    y  // capped — geometric convergence for probability semirings
}

/// Build the differential matrix Df(Y) by multi-variable Leibniz rule.
///
/// For each PackingFactored P with in_scc_children = [c_1, ..., c_m]
/// and target_i:
///   For each position k in 1..=m:
///     Df[target_i][c_k] ⊕= outside_product ⊗ Π_{l < k} Y[c_l]
///                                          ⊗ Π_{l > k} Y[c_l]
fn build_differential_matrix<W: SemiringRef>(
    y: &[W],
    packings: &[PackingFactored<W>],
    n: usize,
) -> Vec<Vec<W>> {
    let mut df = vec![vec![W::zero_ref(); n]; n];
    for p in packings {
        let m = p.in_scc_children.len();
        if m == 0 { continue; }  // exit packings contribute to b, not Df
        for k in 0..m {
            let mut prod = p.outside_product.clone();
            for l in 0..m {
                if l != k {
                    prod = prod.times_ref(&y[p.in_scc_children[l]]);
                }
            }
            let j = p.in_scc_children[k];
            df[p.target_i][j] = df[p.target_i][j].plus_ref(&prod);
        }
    }
    df
}

/// Evaluate f(Y) — for each Symbol in the SCC, compute the
/// total contribution from ALL packings (in-SCC and exit) at
/// the current iterate Y.
fn evaluate_f<W: SemiringRef>(
    y: &[W],
    packings: &[PackingFactored<W>],
    b: &[W],
    n: usize,
) -> Vec<W> {
    let mut f = b.to_vec();
    for p in packings {
        if p.in_scc_children.is_empty() { continue; }
        let mut prod = p.outside_product.clone();
        for &c in &p.in_scc_children {
            prod = prod.times_ref(&y[c]);
        }
        f[p.target_i] = f[p.target_i].plus_ref(&prod);
    }
    f
}
```

### Step 5 — Realize integration (~90 LoC, `wpda_walker.rs`)

At the Symbol arm of `realize_node_leave`, when the Symbol belongs to
a non-trivial SCC:

```rust
let scc_id = scc_of_symbol.get(&id);
if let Some(scc_id) = scc_id {
    if !scc_meta[scc_id.0].is_trivial {
        // Lazily solve the SCC fixpoint if not yet done.
        let solved = scc_meta[scc_id.0].solved_weights.get_or_init(|| {
            let packings: Vec<PackingFactored<W>> = scc_meta[scc_id.0].symbols.iter()
                .flat_map(|&s| sppf.packings_of(s).iter().map(move |&p| (s, p)))
                .map(|(s, p)| factor_scc_packing(sppf, &scc_meta[scc_id.0].symbols, p,
                                                  &scc_meta[scc_id.0].local_idx,
                                                  &memo_outside))
                .collect();
            solve_scc_weights_newton(scc_meta[scc_id.0].symbols.len(), &packings, 64)
        });

        // Now: produce realizations from exit packings only,
        // pre-multiplied by the Newton-solved Y[i] for this symbol.
        let scc_idx_i = scc_meta[scc_id.0].local_idx[&id];
        let multiplier = solved[scc_idx_i].clone();
        let mut out = Vec::new();
        for &s_j in &scc_meta[scc_id.0].symbols {
            for &p in sppf.packings_of(s_j) {
                if is_exit_packing(p, &scc_meta[scc_id.0]) {
                    if let Some(p_results) = memo.get(&p) {
                        for (arg, _w_orig) in p_results {
                            out.push((arg.clone(), multiplier.clone()));
                        }
                    }
                }
            }
        }
        return out;
    }
}
// Singleton-SCC path: existing logic unchanged.
```

**Total**: ~80 + 50 + 60 + 200 + 90 = **~480 LoC production**.

---

## 8. New Trait Requirements

### 1. `StarSemiringRef` trait (~30 LoC in `automata/semiring.rs`)

```rust
/// Star semiring with reference-style operations (no `Copy` required).
///
/// Mirrors `StarSemiring` for the heap-allocated semiring family
/// (e.g., `FreeWeight`, `ParikhWeight<D>`). Operations take `&self`
/// and return owned values.
///
/// **Mathematical content** identical to `StarSemiring`:
/// `star(a) = 1 ⊕ a ⊕ a² ⊕ ... ` (Kleene closure / geometric sum).
pub trait StarSemiringRef: SemiringRef {
    /// Kleene star: `a* = 1 ⊕ a ⊕ a² ⊕ ...`
    fn star_ref(&self) -> Self;
    /// Kleene plus: `a⁺ = a ⊗ a*`
    fn plus_star_ref(&self) -> Self {
        self.times_ref(&self.star_ref())
    }
}

/// Blanket impl: every `StarSemiring` (which requires `Copy`)
/// automatically satisfies `StarSemiringRef`.
impl<T: StarSemiring> StarSemiringRef for T {
    #[inline]
    fn star_ref(&self) -> Self { self.star() }
    #[inline]
    fn plus_star_ref(&self) -> Self { self.plus_star() }
}
```

### 2. `LexicographicWeight: StarSemiring` (~15 LoC in `automata/lex_weight.rs`)

```rust
impl StarSemiring for LexicographicWeight {
    /// Tropical (idempotent) star: `1 ⊕ a ⊕ 2a ⊕ ...`
    /// = `min(0, a, 2a, ...) = 0` when `a ≥ 0`, else `a` (diverges).
    /// For idempotent: `star(a) = 1` always (a ⊕ 1 = 1 absorbs).
    /// Lex tiebreak: inherit `self`'s alt_id/source for determinism.
    fn star(&self) -> Self {
        // Idempotent: `star(a) = 1 ⊕ a = 1` (under `1 ⊒ a` for tropical
        // with a ≥ 0). For lex weights with potentially negative primary
        // (unbounded), this still collapses to one for cycle handling
        // purposes (which is what Phase C's tri-color skip implicitly
        // assumed).
        Self::one()
    }
}
```

### 3. `matrix_star_ref` free function (~30 LoC in `automata/semiring.rs`)

Parallel to existing `matrix_star`, but uses `StarSemiringRef` so it
works with heap-allocated semirings:

```rust
pub fn matrix_star_ref<W: StarSemiringRef>(
    adj: &[Vec<W>],
) -> Vec<Vec<W>> {
    let n = adj.len();
    let mut a: Vec<Vec<W>> = adj.iter().map(|row| row.clone()).collect();
    for k in 0..n {
        let k_star = a[k][k].star_ref();
        for i in 0..n {
            for j in 0..n {
                // a[i][j] = a[i][j] ⊕ a[i][k] ⊗ k_star ⊗ a[k][j]
                let aik = a[i][k].clone();
                let akj = a[k][j].clone();
                let term = aik.times_ref(&k_star).times_ref(&akj);
                a[i][j] = a[i][j].plus_ref(&term);
            }
        }
    }
    a
}
```

### 4. Bound replacement at `wpda_walker.rs`

Change `W: IdempotentSemiring` → `W: SemiringRef + StarSemiringRef` at
the realize entry points (lines 3093, 3116, 3239, 3393). The new bound
is **strictly broader**: every existing `IdempotentSemiring +
CompleteSemiring` already has a `StarSemiring` impl
(semiring.rs:319/521/661/963/1107/2110/2270/2413), so no production
grammar regresses. Adding `LexicographicWeight: StarSemiring` closes
the only gap.

---

## 9. Worked Examples

### Example 1: Direct left recursion (linear, no multi-call)

Grammar: `S → S "+" 1 | 1` (semantic-action computes addition).

Parsing `1+1+1`: SPPF cycle subgraph (after Symbol-dedup):
```text
S_{0,5} ─[+ rule]→ Packing → [S_{0,3}, "+", "1"]
S_{0,3} ─[+ rule]→ Packing → [S_{0,1}, "+", "1"]
S_{0,1} ─[base]→  Packing → ["1"]
```

Are these in the SAME SCC? Only if Symbol-dedup makes `S_{0,1}` and
`S_{0,3}` the same SppfId — which happens only if their `(nt, lo, hi)`
match. They don't (different `hi`). So this is acyclic: each Symbol is
in its own trivial SCC.

**Cycle ARISES** only in grammars like `S → S | num` (unit recursion)
or `S → S | num` with mutual recursion through another nonterminal.
Example:
```text
S → A | num
A → S
```

Parsing `num`: SPPF has `S_{0,1}` and `A_{0,1}`, both reachable from
each other through:
```text
S_{0,1} ─[unit]→ Packing → [A_{0,1}]
A_{0,1} ─[unit]→ Packing → [S_{0,1}]
```

This IS a 2-SCC: `{S_{0,1}, A_{0,1}}`. Each Symbol has exactly one
in-SCC child per packing — **LINEAR**. Newton's linear fast-path
activates and runs single-shot Lehmann.

Matrix:
```text
A = [ 0  c(S→A) ]      b = [ c(S→num)⊗Y_num ]
    [ c(A→S)  0 ]          [ 0               ]
```

Lehmann gives `A* = (I⊕A)*`. For LexicographicWeight, `A* = I` (idempotent
tropical: anything ⊕ 1 = 1). Closed `Y_S = b[0] = c(S→num) ⊗ Y_num`.
This is exactly the answer we'd get from cycle-skip.

For LogWeight (`p = c(S→A), q = c(A→S)`): `A*` gives
`Y_S = (1 / (1 - p·q)) · b[0] = c(S→num) · Y_num / (1 - p·q)`. This is
the correct probabilistic inside weight; cycle-skip would give just
`c(S→num) · Y_num` (off by the geometric factor).

### Example 2: Binary operator (multi-call, Newton)

Grammar: `S → S "+" S | num`.

Parsing the empty span `ε` of `A → A A | ε` (a degenerate but
mathematically clean example): SPPF has `S_{0,0}` with two packings:
- `P1: S_{0,0} ← [S_{0,0}, S_{0,0}]` (multi-call! both children are
  the same in-SCC Symbol)
- `P2: S_{0,0} ← ε` (exit packing)

SCC = `{S_{0,0}}` (singleton with self-loop), so non-trivial.

Linear fast-path check: `P1.in_scc_children.len() = 2`. **NOT LINEAR**
— Newton activates.

The fixpoint equation: `Y = c(P1) ⊗ Y ⊗ Y ⊕ c(P2) ⊗ Y_ε`.

Let `a = c(P1) ⊗ outside-of-P1` (no outside; just `c(P1)`) and
`b = c(P2) ⊗ Y_ε`. Then: `Y = aY² ⊕ b`.

Newton iteration:
- `Y^{(0)} = 0`
- Iteration 1:
  - `Df(Y^{(0)}) = Df(0)[0][0] = a ⊗ Y^{(0)} + Y^{(0)} ⊗ a = 0` (Leibniz)
  - `Df* = I*`. For most semirings, `0* = 1`. So `Df* = [[1]]`.
  - `f(Y^{(0)}) = a·0·0 ⊕ b = b`.
  - `Y^{(1)} = Df*[0][0] ⊗ f(Y^{(0)})[0] = 1 ⊗ b = b`.
- Iteration 2:
  - `Df(b) = a ⊗ b ⊕ b ⊗ a = 2ab` (under non-idempotent ⊕; for
    idempotent it's just `ab`).
  - `Df* = (2ab)* `.
  - `f(b) = a·b·b ⊕ b = ab² ⊕ b`.
  - `Y^{(2)} = (2ab)* ⊗ (ab² ⊕ b)`.

For probabilities (`a, b ∈ (0, 1)`), this is the Catalan generating
function evaluated at `(a, b)`. The iteration converges geometrically.

Under LexicographicWeight (idempotent): `(2ab)* = 1`, `ab² ⊕ b = b`
(since `b ⊒ ab²` for `a ≤ 1`). So `Y^{(2)} = b`. Fixed point reached.

### Example 3: Mutual recursion with multi-call

Grammar: `S → A B | num; A → S | a; B → S | b`.

Parsing some input creates SCC = `{S, A, B}` (size 3). Packing for
`S` is `S ← [A, B]` — multi-call. Newton activates.

The fixpoint:
```text
Y_S = Y_A ⊗ Y_B ⊕ c(num)
Y_A = Y_S ⊕ c(a)
Y_B = Y_S ⊕ c(b)
```

This is the canonical "bilinear" multi-call case. Newton iterates over
the 3×3 differential matrix. Convergence in O(3) iterations for
idempotent; geometric for probabilities.

---

## 10. Test Plan

### Unit tests (in `prattail/src/automata/semiring.rs` `#[cfg(test)] mod`)

| ID | Description |
|----|-------------|
| **CSCH-1** | `tarjan_sccs` on linear chain SPPF (3 Symbols, no cycle) returns 3 singleton SCCs in topological order. |
| **CSCH-2** | `tarjan_sccs` on unit cycle `Sym_A → Pack_P → Sym_A` returns 1 SCC of size 1 with self-loop edge detected. |
| **CSCH-3** | `tarjan_sccs` on mutual recursion `Sym_A ↔ Sym_B` returns 1 SCC of size 2. |
| **CSCH-4** | `build_differential_matrix` on synthetic 1-packing SCC: `P: S ← S ⊗ S`. Verify `Df(Y)[0][0] = 2·Y` (Leibniz). |
| **CSCH-5** | `solve_scc_weights_newton` on 2×2 mutual-recursion under `LogWeight`. Verify closed-form `Y_A = (p · q · Y_num) / (1 - p·q · ...)` matches by hand. |
| **CSCH-6** | `solve_scc_weights_newton` on 1-Symbol SCC with `A → A A | ε` under `CountingWeight`. Verify saturation to `u64::MAX`. |
| **MCSL-1** | `S → S S | ε` under `BooleanWeight`. Hand: `Y = ε ⊕ Y⊗Y`; closed form `Y = true`. Newton converges in 1 step (idempotent fast path). |
| **MCSL-2** | Same grammar under `CountingWeight` parsing `aaa`. Verify path count saturates or equals Catalan number. |
| **MCSL-3** | Differential against analytic Jacobian for arity-3 packing `P: S_i ← S_j ⊗ S_k ⊗ S_l`. Verify `Df(Y)[i][j] = outside · Y_k · Y_l`. |
| **MCSL-4** | Linear fast-path detection — synthesize SCC with only unary in-SCC packings, assert exactly 1 Newton iteration. |
| **CSCH-7** | `matrix_star_ref` reproduces `matrix_star` for Copy semirings (regression guard). |
| **CSCH-8** | `LexicographicWeight::star()` returns `Self::one()` (idempotent collapse). |

### Integration tests (in `languages/tests/`)

| ID | Description |
|----|-------------|
| **CSCH-INT-1** | Parse `bigint(bool(true))` from calculator with `LogWeight` instantiation; assert ≥ 1 term + finite log-probability weight. |
| **CSCH-INT-2** | Synthetic grammar `S → S | a` (direct unit cycle), parse `a`, `W = CountingWeight`. Assert path count saturates. Under `LexicographicWeight` same test returns 1 derivation (idempotent collapse). |
| **CSCH-INT-3** | Differential test: same SPPF, two W instantiations (`LexicographicWeight`, `LogWeight`). LexicographicWeight equals current tri-color-skip result; LogWeight differs (proves matrix-star activates). |
| **MCSL-5** | Calculator's `Or . a:Proc, b:Proc |- a "or" b : Proc`, parse `true or false or true`, `W = LogWeight` with uniform rule probabilities. Assert finite log-weight, no NaN/Inf. Compare against direct enumeration. |
| **MCSL-6** | Differential test for multi-call: same SPPF, `LexicographicWeight` vs `LogWeight`. Both succeed; LogWeight result STRICTLY exceeds 1-iteration Lehmann result, confirming Newton activated. |

**Gap acknowledged**: of the 6500+ existing tests, NONE currently
exercise non-idempotent semirings on cyclic SPPFs. CSCH-INT-1..3 and
MCSL-5..6 are the first validators.

---

## 11. Migration Strategy — Staged (3 commits)

### Commit 1 — Trait extension only

**Files**: `automata/semiring.rs`, `automata/lex_weight.rs`.

**Changes**:
- Add `StarSemiringRef` trait + blanket `impl<T: StarSemiring>
  StarSemiringRef for T`.
- Add `matrix_star_ref` free function.
- Add `impl StarSemiring for LexicographicWeight`.

**Gate**: existing 6500+ tests still pass (additive only, zero
behavioral change).

### Commit 2 — Detection + factoring + Newton infrastructure (unwired)

**Files**: `sppf.rs`, `semiring.rs`, test mods.

**Changes**:
- Add `tarjan_sccs`, `PackingFactored<W>`, `factor_scc_packing` in
  `sppf.rs`.
- Add `solve_scc_weights_newton`, `build_differential_matrix`,
  `evaluate_f` in `semiring.rs` (or new `cycle_solve.rs` module).
- Add CSCH-1..8 + MCSL-1..4 unit tests.
- All helpers marked `#[allow(dead_code)]` until wired in Commit 3.

**Gate**: helpers tested but unwired; gauntlet still green.

### Commit 3 — Wire Newton into `realize_root_to_terms_with_weights`

**Files**: `wpda_walker.rs`, `languages/tests/*`.

**Changes**:
- Replace `W: IdempotentSemiring` bounds with `W: StarSemiringRef`.
- Pre-compute `scc_of` and `scc_meta` at entry to
  `realize_root_to_terms_with_weights`.
- At Symbol Leave: dispatch on `is_trivial`. Trivial → existing
  path. Non-trivial → lazy `solve_scc_weights_newton` + multiplier
  application to exit packings.
- Add CSCH-INT-1..3 + MCSL-5..6 integration tests.

**Gate**: full gauntlet — 6500+ tests under `LexicographicWeight`
unchanged; 5 new tests under `LogWeight`/`CountingWeight` pass; MCSL-6
differential test confirms Newton iterates beyond Lehmann's 1-shot for
multi-call.

### Why staged (not atomic)

Each commit isolates one concern:
- Commit 1: trait infrastructure (compile-only).
- Commit 2: algorithmic correctness on synthetic data (unit-tested).
- Commit 3: real-world integration (gauntlet-tested).

This matches the proven Phase C cadence (Q1/Q2/Q3/Q4 four commits).
A single atomic commit would obscure which gate uncovers which
regression and is harder to revert if a layer turns out wrong.

---

## 12. LoC Estimate

| Phase | File | Production LoC | Test LoC |
|-------|------|----------------|----------|
| Trait extension | `automata/semiring.rs` | +60 | 0 |
| `LexicographicWeight::star` | `automata/lex_weight.rs` | +15 | +20 |
| `matrix_star_ref` | `automata/semiring.rs` | +30 | +40 (CSCH-7) |
| Tarjan SCC | `sppf.rs` | +80 | +60 (CSCH-1..3) |
| `PackingFactored` + `factor_scc_packing` | `sppf.rs` | +60 | +30 |
| `solve_scc_weights_newton` (linear + Newton + helpers) | `automata/semiring.rs` | +200 | +180 (CSCH-4..6, MCSL-1..4) |
| Realize integration | `wpda_walker.rs` | +90 | 0 |
| Integration tests | `languages/tests/*` | 0 | +180 (CSCH-INT-1..3, MCSL-5..6) |
| **Total** | | **~535** | **~510** |

**Grand total: ~1045 LoC** (~535 production + ~510 tests).

Above the original 300-500 estimate because:
- The new `StarSemiringRef` trait + blanket impl weren't previously counted.
- Newton's method properly handles multi-call SCCs (replacing the
  pessimistic stopgap).
- Test coverage is substantial (none exists today — including new
  tests for the multi-call case under non-idempotent semirings).

---

## 13. Mandate Compliance

### P1 — Preserve all derivations: **STRENGTHENED**

The current tri-color skip *discards* the cyclic packing entirely
when its memo Vec is empty and color is Gray. Newton's method
*integrates* its contribution into the inside weight. Term enumeration
(which SPPF tree shapes are realized) is unchanged — we still produce
one realized `ActionArg` per exit packing. But the **weight** on each
realized term now correctly reflects the closed-semiring sum of all
infinite cyclic paths reaching that term, rather than dropping cyclic
contributions.

This is **more** P1-aligned than the status quo. Cycle-skip was an
approximation justified by idempotency; Newton + matrix-star is the
exact aggregation.

### P2 — Rule out by evidence: **SATISFIED**

Newton's iterates monotonically increase (`Y^{(n+1)} ⊒ Y^{(n)}`); no
term is dropped silently. Rules contribute zero only when their
closed-semiring weight is genuinely zero (e.g., the rule's weight is
the additive identity, or all its children resolve to zero). That's
evidence-driven rule-out, not weight-based pruning.

For `CountingWeight` on cycles, the result saturates to `u64::MAX` —
which IS evidence: "this grammar admits unbounded ambiguity for this
input." The caller can detect saturation and respond appropriately.

### P3 — Semiring `⊕` at merge: **SATISFIED EXACTLY**

The closed inside-weight `Y_i = (A* ⊗ b)[i]` (or its Newton-iterated
analog for non-linear systems) is PRECISELY the `⊕`-aggregation
`I ⊕ A ⊕ A² ⊕ ...` of all cyclic paths through Symbol `s_i`. This is
the defining `⊕`-merge for the cyclic case.

The current stopgap distributing `outside_product` into each
multi-call slot is a P3 violation: it sums a missing product, not a
missing sum. Newton's multi-variable Leibniz differential is the
correct treatment.

---

## 14. Trade-offs (Honest Accounting)

### Gained

- **Lifted `IdempotentSemiring` bound** on cyclic realize. Enables:
  - `CountingWeight` — count derivations of a cyclic grammar.
  - `LogWeight` — log-probability inside weights for probabilistic CFGs.
  - `EntropyWeight` — entropy aggregation across parse forests.
  - `NBest` — n-best derivation enumeration with semiring weights.
- **Mathematically principled**. Matches Opedal §6 + Lehmann 1977 +
  Esparza-Kiefer-Luttenberger 2007.
- **Reuses existing infrastructure**:
  - `matrix_star` (semiring.rs:2748), well-tested for Boolean/Tropical/
    Arctic/Counting.
  - Iterative Tarjan reference (buchi.rs:798).
  - Phase C's `Packing.weight` / `Symbol.weight_sum` shape.
  - The established realize trampoline.
- **No walker rewrite, no codegen change, no grammar IR change.**
- **Common case zero-overhead**: linear fast-path detection means
  unary/transitive SCCs run with the exact same cost as the original
  Lehmann-only plan (which itself was within constant factors of the
  current tri-color skip).

### Lost

- **Simplicity of the 5-line cycle-skip** in `realize_node_leave`
  becomes ~480 LoC of dispatch + factoring + Newton iteration +
  Leibniz differential. Mitigated: the per-realize cost is paid
  ONLY for non-trivial SCCs (Phase C's empirical sweep showed
  < 1 % of realize calls).
- **One new trait** (`StarSemiringRef`) deepens the semiring
  hierarchy. Mitigated by the blanket impl: every existing
  `StarSemiring` automatically satisfies it.
- **Newton-iteration cap** (`max_iters = 64`) introduces a
  configurable hyper-parameter. Default chosen for `LogWeight`
  convergence to ~1e-15 precision; documented.
- **Mathematical complexity**: maintainers must understand Lehmann's
  algorithm + Newton-Raphson + multi-variable Leibniz rule.
  Mitigated by extensive inline documentation + references to the
  Esparza-Kiefer-Luttenberger and Opedal papers.

---

## 15. Interactions with Other Phases

### Phase F (cursor.builder deletion) — ORTHOGONAL

Phase F removes `cursor.builder` reads from the walker. The realize
path (`realize_root_to_terms_with_weights`) already uses a *fresh*
`SemanticBuilder` in `realize_packing_call` (line ~3527) — it is
independent of `cursor.builder`. The matrix-star + Newton integration
happens entirely inside `realize_root_to_terms_with_weights`,
downstream of any `cursor.builder` semantics. The two phases compose
without interference; either order works.

### Phase C's `Sppf<W>` invariants — COMPATIBLE

Matrix-star + Newton are *post-processing computations* over the SPPF
arena. They do not mutate `nodes`, `text_arena`, or `symbol_packings`.
The **append-only arena guarantee is preserved** (Newton produces
temporary `Vec<Vec<W>>` matrices that live only for the duration of
one realize call; nothing is cached or written back to the arena).

The `weight_sum` aggregation invariant on `Symbol` nodes is
**unchanged** — that's still the link-time `⊕`-monotone aggregation;
Newton is an *additional* derived computation that the realize path
requests, not a replacement for `weight_sum`.

Checkpoint/restore semantics are preserved (Newton operates on the
runtime-realize view of the arena, not on its persistent state).

### Realize action invocation — UNCHANGED

The action functions (codegen-emitted `action_fn`) are invoked in
`realize_packing_call` via a fresh `SemanticBuilder`. Newton modifies
only the weight scalar that pre-multiplies the realized `ActionArg`
values. The action functions themselves are unaffected.

---

## 16. Risk Register

| Risk | Severity | Mitigation |
|------|----------|------------|
| Tarjan SCC has a bug on edge cases (single-node self-loop, empty SCC) | MED | CSCH-1..3 unit tests; comparison with iterative reference at buchi.rs:798. |
| Newton diverges for adversarial LogWeight inputs (`p > 1` interpreted as probability) | LOW-MED | `max_iters` cap; existing `LogWeight::star` returns `zero()` on divergence. |
| Multi-call differential computation has off-by-one in Leibniz | MED | CSCH-MCSL-3 explicit test against analytic Jacobian for arity-3 packing. |
| `LexicographicWeight::star` returning `Self::one()` doesn't preserve lex tiebreaks | LOW | Lex tiebreak only matters for `⊕`-equal weights; under idempotency, all `star` results compress to the absorbing element. |
| Realize integration's "exit packing" detection is wrong (includes/excludes the wrong ones) | MED | Explicit test that exit packings = packings with `in_scc_children.is_empty()`. |
| Performance regression on the common (acyclic) case due to Tarjan overhead | LOW | Tarjan is O(V+E), same asymptotic as the DFS we already do. The trivial-SCC fast path skips Newton entirely. |

---

## 17. Performance Analysis

### Worst case

For an SCC of size `n` with `m` multi-call packings of max arity `k`:
- Per-iteration cost: `O(n³)` for `matrix_star_ref` (Lehmann) + `O(m·k)`
  for differential construction.
- Number of iterations:
  - Idempotent semirings: `O(n)` (Esparza Theorem 5.1).
  - Probability semirings: `O(log(1/ε))` for `ε`-precision; cap at 64.
- **Total cyclic-realize cost**: `O(n⁴ + n·m·k)` per non-trivial SCC.

### Common case (no cycles)

- Tarjan: `O(V + E)` linear pass.
- All SCCs trivial; Newton not invoked.
- **Total**: linear pass over reachable SPPF subgraph. Same asymptotic as
  the current tri-color DFS, with slightly higher constant factor for
  Tarjan's lowlink tracking.

### Empirical estimate

Phase C's sweep showed `< 1 %` of realizes had non-trivial cycles. Of
those, typical SCC size `k ≤ 5`, max arity `≤ 4`. So worst-case cyclic
overhead is `O(5⁴ + 5·m·4) ≈ O(625 + 20m)`, which is negligible
compared to the cartesian-product realize loop (`O(N^K)` where `N` is
packing count and `K` is rule arity, easily into the thousands per
realize).

### Linear fast-path optimization

When all multi-call packings have `in_scc_children.len() ≤ 1`, the
implementation skips Newton iterations entirely and runs single-shot
Lehmann. This is byte-equivalent in operation count to the original
Lehmann-only plan, which itself was within constant factors of the
current tri-color skip. **No performance regression on the common
case.**

---

## 18. Numerical Stability for Floating-Point Semirings

### LogWeight

Operations in log space:
- `⊕` = `log_sum_exp` (numerically stabilized via factoring out the max).
- `⊗` = `+` (simple addition).
- `star` = `log(1/(1-exp(p)))` = `-log(1 - exp(p))`. Diverges when
  `p ≥ 0` (probability ≥ 1); existing `LogWeight::star` returns
  `Self::zero()` in that case.

Newton iterations under LogWeight:
- Build `Df(Y)` matrix: each entry is a product of `Y_k` values in
  log space (= sum), so no catastrophic cancellation.
- `matrix_star_ref(Df)`: invokes `star` on diagonal entries, then
  combines via `⊕` and `⊗`. Each `star` call is independent
  numerically; combination uses `log_sum_exp` which is stable.
- Update `Y^{(n+1)} = Df* ⊗ f(Y^{(n)})`: a single matrix-vector
  product in log space.

**Conclusion**: numerical stability is identical to a single matrix-star
call; Newton just iterates the same primitives.

### EntropyWeight

The expectation component is bounded above by the weight component's
geometric sum. As long as the weight component doesn't diverge (handled
by `star`'s zero-return on divergence), entropy is finite.

### CountingWeight

Saturation arithmetic (caps at `u64::MAX`); no precision issues.

### LexicographicWeight (production W)

Idempotent tropical; `star` collapses to identity. No precision
concerns — purely structural.

---

## 19. References

1. **Opedal, A., et al. (2023)**. "Efficient Semiring-Weighted Earley
   Parsing." *Proceedings of ACL 2023*.
   [PDF](https://www.cs.jhu.edu/~jason/papers/opedal+al.acl23.pdf).
   Source for the closed-semiring cycle handling technique (§6, App E).

2. **Goodman, J. (1999)**. "Semiring Parsing." *Computational
   Linguistics* 25(4), 573-605.
   [PDF](https://aclanthology.org/J99-4004.pdf). The foundational
   reference for semiring-weighted CFG parsing.

3. **Lehmann, D. J. (1977)**. "Algebraic Structures for Transitive
   Closure." *Theoretical Computer Science* 4(1), 59-76. The original
   matrix-star algorithm for closed semirings.

4. **Esparza, J., Kiefer, S., Luttenberger, M. (2007)**. "An Extension
   of Newton's Method to ω-Continuous Semirings." *Proceedings of
   DLT 2007*. The proper handling of non-linear polynomial systems
   over closed semirings.

5. **Etessami, K., Yannakakis, M. (2009)**. "Recursive Markov Chains,
   Stochastic Grammars, and Monotone Systems of Nonlinear Equations."
   *Journal of the ACM* 56(1), Article 1. Convergence analysis for
   monotone polynomial fixpoints (including probabilistic context-free
   grammars).

6. **Stolcke, A. (1995)**. "An Efficient Probabilistic Context-Free
   Parsing Algorithm that Computes Prefix Probabilities."
   *Computational Linguistics* 21(2), 165-201.
   [PDF](https://aclanthology.org/J95-2002.pdf). Sister reference for
   the prefix-weight computation in Opedal §6.1.

7. **Scott, E., Johnstone, A. (2010)**. "GLL Parsing." *ENTCS* 253(7),
   177-189. The SPPF construction discipline we use.

8. **Tarjan, R. (1972)**. "Depth-First Search and Linear Graph
   Algorithms." *SIAM Journal on Computing* 1(2), 146-160. The
   classical SCC algorithm.

---

## 20. Critical Files for Implementation

| File | Lines | Purpose |
|------|-------|---------|
| `prattail/src/wpda_walker.rs` | 3022-3650 (realize machinery) | Add SCC-aware dispatch in `realize_root_to_terms_with_weights`; replace tri-color skip with Newton solve for non-trivial SCCs. |
| `prattail/src/sppf.rs` | 137-263 (`SppfNode`) + 355-600 (`Sppf` impl) | Add `tarjan_sccs`, `PackingFactored<W>`, `factor_scc_packing`. |
| `prattail/src/automata/semiring.rs` | 79-166 (trait hierarchy) + 2748-2783 (existing `matrix_star`) | Add `StarSemiringRef`, `matrix_star_ref`, `solve_scc_weights_newton`, `build_differential_matrix`, `evaluate_f`. |
| `prattail/src/automata/lex_weight.rs` | 1-60 (impl block) | Add `impl StarSemiring for LexicographicWeight`. |
| `prattail/src/buchi.rs` | 798-851 (iterative Tarjan reference) | Read-only reference for the iterative SCC algorithm; copy/adapt to `sppf.rs::tarjan_sccs`. |
| `languages/tests/cycle_handling_tests.rs` (NEW FILE) | — | CSCH-INT-1..3 + MCSL-5..6 integration tests. |
